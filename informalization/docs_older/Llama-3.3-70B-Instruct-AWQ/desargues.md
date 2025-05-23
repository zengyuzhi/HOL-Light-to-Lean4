# desargues.ml

## Overview

Number of statements: 52

The `desargues.ml` file formalizes Desargues's theorem, a fundamental concept in projective geometry. It builds upon the `Multivariate/cross.ml` module, suggesting a connection to multivariate polynomial operations. The file likely contains definitions and proofs related to Desargues's theorem, which states that two triangles are perspective if and only if they are axially perspective. This theorem is a key result in geometry, and its formalization in HOL Light enables rigorous reasoning and verification of geometric properties.

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
* The proof starts by generalizing the statement for all `u` and `v` using `REPEAT GEN_TAC`.
* It then applies symmetry of orthogonality using `ONCE_REWRITE_TAC[ORTHOGONAL_SYM]`.
* The `ORTHOGONAL_TO_SUBSPACE_EXISTS` theorem is instantiated with `{u:real^3,v}` to find a vector orthogonal to the subspace spanned by `u` and `v`.
* The proof involves rewriting and simplification steps using `REWRITE_TAC` and `SIMP_TAC` with various theorems and definitions, including `FORALL_IN_INSERT`, `NOT_IN_EMPTY`, `DIMINDEX_3`, `DIM_LE_CARD`, `FINITE_INSERT`, `FINITE_EMPTY`, and `CARD_CLAUSES`.
* The existence of a non-zero vector `w` is established using `EXISTS_TAC` with `CARD {u:real^3,v}`.
* The proof concludes with `ARITH_TAC`, which performs arithmetic simplifications.

### Mathematical insight
This theorem is related to the concept of orthogonality in vector spaces and is a step towards proving more complex geometric or algebraic results, such as Desargues's theorem, as hinted in the comment. The existence of a non-zero vector orthogonal to two given vectors in 3D space has implications for understanding the geometric and algebraic structure of vector spaces.

### Dependencies
* Theorems:
  + `ORTHOGONAL_TO_SUBSPACE_EXISTS`
  + `ORTHOGONAL_SYM`
* Definitions:
  + `orthogonal`
  + `vec`
  + `real^3`
* Other:
  + `DIMINDEX_3`
  + `FORALL_IN_INSERT`
  + `NOT_IN_EMPTY`
  + `DIM_LE_CARD`
  + `FINITE_INSERT`
  + `FINITE_EMPTY`
  + `CARD_CLAUSES`

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to the handling of vector spaces, orthogonality, and the instantiation of theorems like `ORTHOGONAL_TO_SUBSPACE_EXISTS`. Differences in how binders and quantifiers are treated, as well as the availability of similar tactics or automation, may require adjustments to the proof strategy.

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
The `direction_tybij` type definition introduces a new type "direction" with constructors `mk_dir` and destructor `dest_dir`, defined for all real vectors `x` of dimension 3, such that `x` is not equal to the zero vector.

### Informal sketch
* The definition relies on the `MESON` tactic, which applies a set of given theorems (`BASIS_NONZERO`, `LE_REFL`, `DIMINDEX_GE_1`) to prove the existence of a non-zero vector in 3-dimensional real space.
* The `?x:real^3` syntax indicates a universal quantification over all vectors `x` in 3-dimensional real space.
* The condition `~(x = vec 0)` ensures that the vector `x` is not the zero vector.
* The `new_type_definition` construct defines a new type "direction" with the specified properties.

### Mathematical insight
The `direction_tybij` type definition provides a way to represent directions in 3-dimensional space, excluding the zero vector. This is a fundamental concept in geometry and is essential for various mathematical and physical applications.

### Dependencies
* Theorems:
  + `BASIS_NONZERO`
  + `LE_REFL`
  + `DIMINDEX_GE_1`
* Definitions:
  + `real`
  + `vec`
* Inductive rules: None

### Porting notes
When porting this definition to other proof assistants, note that the `MESON` tactic may not have a direct equivalent. Instead, the proof may need to be reconstructed using the specific tactics and mechanisms available in the target system. Additionally, the representation of vectors and the zero vector may differ between systems, requiring adjustments to the definition and proof.

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
Two vectors `x` and `y` are perpendicular (`_ _|_`) if and only if the destination directions (`dest_dir`) of `x` and `y` are orthogonal.

### Informal sketch
* The definition `perpdir` introduces a new relation `_ _|_` between vectors `x` and `y`.
* This relation is defined in terms of the `orthogonal` relation between the destination directions (`dest_dir`) of `x` and `y`.
* To prove that two vectors are perpendicular, one would need to show that their destination directions are orthogonal, using the `orthogonal` relation.

### Mathematical insight
The `perpdir` definition provides a way to express the perpendicularity of two vectors in terms of their destination directions. This is a fundamental concept in geometry and linear algebra, and is likely used as a building block for more complex geometric constructions and theorems.

### Dependencies
* `orthogonal`
* `dest_dir`

### Porting notes
When porting this definition to another proof assistant, note that the `new_definition` syntax may not be directly equivalent. In Lean, for example, this might be expressed using a `def` statement, while in Coq it might be expressed using a `Definition` statement. Additionally, the `orthogonal` relation and `dest_dir` function will need to be defined or imported in the target system.

---

## pardir

### Name of formal statement
pardir

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let pardir = new_definition `x || y <=> (dest_dir x) cross (dest_dir y) = vec 0;;
```

### Informal statement
The `pardir` definition states that two vectors `x` and `y` are parallel (`x || y`) if and only if the cross product of their destination directions (`dest_dir x` and `dest_dir y`) equals the zero vector (`vec 0`).

### Informal sketch
* The definition relies on the notion of the cross product of two vectors being zero, indicating the vectors are parallel.
* It utilizes the `dest_dir` function to extract the direction of each vector.
* The `pardir` relation is then defined as an equivalence between the parallel condition and the cross product condition.

### Mathematical insight
The `pardir` definition provides a way to determine if two vectors are parallel based on their cross product, which is a fundamental concept in linear algebra and geometry. This definition is important for establishing properties and theorems about parallel vectors in subsequent developments.

### Dependencies
* `dest_dir`
* `cross`
* `vec 0`

### Porting notes
When translating this definition into another proof assistant, ensure that the cross product operation and the zero vector are defined and handled correctly. Additionally, the `dest_dir` function needs to be ported or have an equivalent in the target system. Pay attention to how vectors and their operations are represented, as this may vary between systems.

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
For all predicates `P`, the following two statements are equivalent: 
1. For all `x`, `P` applied to the destination direction of `x` holds.
2. For all `x` not equal to the zero vector, `P` applied to `x` holds.
Additionally, the following two statements are equivalent:
1. There exists an `x` such that `P` applied to the destination direction of `x` holds.
2. There exists an `x` not equal to the zero vector such that `P` applied to `x` holds.

### Informal sketch
* The proof involves establishing two equivalences related to a predicate `P` and the `dest_dir` function.
* The first equivalence is between a universal statement about `P` applied to `dest_dir x` and a universal statement about `P` applied to `x` with the condition that `x` is not the zero vector.
* The second equivalence is between an existential statement about `P` applied to `dest_dir x` and an existential statement about `P` applied to `x` with the same condition.
* The `MESON_TAC` tactic is used in conjunction with `direction_tybij`, suggesting that the proof involves meson-style reasoning and possibly properties of `dest_dir` and its relationship to vectors.

### Mathematical insight
This statement provides a way to relate properties of the destination direction of vectors to properties of the vectors themselves, under the condition that the vectors are not zero. It's useful for transferring results or properties known about directions to the vectors that have those directions, leveraging the `dest_dir` function.

### Dependencies
* `direction_tybij`

### Porting notes
When translating this into another proof assistant, pay close attention to how the new system handles predicates, vector operations, and the specific `dest_dir` function. The `MESON_TAC` tactic may not have a direct counterpart, so understanding the underlying proof steps and how they can be replicated using the target system's tactics or automation will be crucial. Additionally, consider how the target system represents and manipulates vectors and their properties, as this may affect how the `dest_dir` function and its properties are defined and used.

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
  * Reflexivity: each element is parallel to itself
  * Symmetry: if `x` is parallel to `y`, then `y` is parallel to `x`
  * Transitivity: if `x` is parallel to `y` and `y` is parallel to `z`, then `x` is parallel to `z`
* The `REWRITE_TAC` with `[pardir; DIRECTION_CLAUSES]` suggests using rewrite rules related to the `pardir` definition and direction clauses to simplify the statements
* `VEC3_TAC` implies a vector-based tactic, potentially simplifying or analyzing the properties in a three-dimensional vector space context

### Mathematical insight
This theorem establishes fundamental properties of the parallel relation, which is crucial in geometric and spatial reasoning. The parallel relation is reflexive, symmetric, and transitive, making it an equivalence relation. This is essential in various mathematical and computational contexts, such as geometry, computer graphics, and physics.

### Dependencies
* `pardir`
* `DIRECTION_CLAUSES`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles equality, symmetry, and transitivity properties. Specifically, consider how to express the `pardir` relation and how to apply rewrite rules or similar mechanisms to simplify the proof. Additionally, be aware of the differences in tactic languages and how vector operations are handled in the target system.

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
For all `x` and `y`, the equivalence `((||) x = (||) y)` holds if and only if `x` is parallel to `y`.

### Informal sketch
* The proof starts by applying the `REWRITE_TAC` tactic with `FUN_EQ_THM` to transform the equivalence into a more manageable form.
* Then, it uses `MESON_TAC` to derive the conclusion from the given premises, specifically leveraging the properties `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS`.
* The `PARDIR_REFL` property is used to establish the reflexive nature of the parallel relation.
* The `PARDIR_SYM` property is used to establish the symmetric nature of the parallel relation.
* The `PARDIR_TRANS` property is used to establish the transitive nature of the parallel relation.

### Mathematical insight
This theorem provides a fundamental property of parallelism, stating that two lines are parallel if and only if their directions are equal. The theorem relies on the reflexive, symmetric, and transitive properties of parallelism, which are essential in establishing the equivalence.

### Dependencies
* Theorems:
  * `PARDIR_REFL`
  * `PARDIR_SYM`
  * `PARDIR_TRANS`
  * `FUN_EQ_THM`
* Definitions:
  None

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of the `||` operator and the `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS` properties. Ensure that these properties are defined and used correctly in the target system. Additionally, the `REWRITE_TAC` and `MESON_TAC` tactics may need to be replaced with equivalent tactics in the target system.

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
For all points `p` and `p'` in 3D real space, if `p` and `p'` are not parallel, then there exists a line `l` such that both `p` is perpendicular to `l` and `p'` is perpendicular to `l`. Furthermore, for any line `l'` such that `p` is perpendicular to `l'` and `p'` is perpendicular to `l'`, `l'` must be parallel to `l`.

### Informal sketch
* The proof starts by assuming two points `p` and `p'` that are not parallel.
* It then applies `REWRITE_TAC` with `perpdir`, `pardir`, and `DIRECTION_CLAUSES` to set up the geometric relationships between points and lines.
* The tactic `REPEAT STRIP_TAC` is used to strip away the universal quantifiers and implications, exposing the core geometric claim.
* The `MP_TAC` with `NORMAL_EXISTS` is applied to introduce the existence of a line `l` that satisfies the perpendicular conditions for both `p` and `p'`.
* `MATCH_MP_TAC MONO_EXISTS` is then used to establish the uniqueness of such a line up to parallelism.
* Finally, `POP_ASSUM_LIST` and `VEC3_TAC` are applied to conclude the proof by handling the geometric constraints in 3D space.

### Mathematical insight
This axiom formalizes a fundamental geometric property: given two non-parallel points in 3D space, there exists a unique line (up to parallelism) to which both points are perpendicular. This is crucial for establishing the consistency and completeness of geometric constructions in 3D space.

### Dependencies
#### Theorems
* `NORMAL_EXISTS`
* `MONO_EXISTS`
#### Definitions
* `perpdir`
* `pardir`
* `DIRECTION_CLAUSES`

### Porting notes
When translating this axiom into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles geometric definitions and theorems, especially regarding perpendicularity and parallelism. Additionally, the use of `REWRITE_TAC`, `MP_TAC`, and `MATCH_MP_TAC` may need to be adapted to the target system's tactic language, considering differences in how these systems manage quantifiers, implications, and existential proofs.

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
* The proof involves finding a point `p` that is orthogonal to two given lines `l` and `l'`.
* The `REWRITE_TAC` tactic is used with `perpdir` and `DIRECTION_CLAUSES` to rewrite the goal in terms of orthogonal directions.
* The `MESON_TAC` tactic is then applied with `NORMAL_EXISTS` and `ORTHOGONAL_SYM` to establish the existence of the point `p` that satisfies the orthogonality conditions for both lines.

### Mathematical insight
This axiom provides a fundamental property about the existence of points orthogonal to given lines, which is crucial in geometric constructions and proofs. It ensures that for any two lines, there is a point that is perpendicular to both, which is a basic requirement in various geometric and spatial reasoning tasks.

### Dependencies
* `perpdir`
* `DIRECTION_CLAUSES`
* `NORMAL_EXISTS`
* `ORTHOGONAL_SYM`

### Porting notes
When translating this axiom into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles existential quantification and orthogonality relations. The `REWRITE_TAC` and `MESON_TAC` tactics may have direct counterparts or require manual rewriting and application of similar tactics to achieve the same proof structure. Additionally, the handling of `NORMAL_EXISTS` and `ORTHOGONAL_SYM` may vary, requiring adjustments to ensure the proof goes through in the target system.

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
* The proof starts by assuming the conditions on `p`, `p'`, and `p''` regarding their non-parallel relationships.
* It then applies `REWRITE_TAC` with `perpdir`, `pardir`, and `DIRECTION_CLAUSES` to transform the goal.
* The `MAP_EVERY` tactic is used to apply `EXISTS_TAC` and `SIMP_TAC` with `BASIS_NONZERO`, `DIMINDEX_3`, and `ARITH` to each of the basis vectors `basis 1 :real^3`, `basis 2 :real^3`, and `basis 3 :real^3`.
* Finally, `VEC3_TAC` is applied to conclude the proof.
* Key steps involve recognizing the geometric implications of the `perpdir` and `pardir` relations and leveraging the properties of the basis vectors in three-dimensional space.

### Mathematical insight
This axiom formalizes a fundamental geometric property related to directions and perpendicularity in three-dimensional space. It is crucial for establishing the consistency and completeness of geometric constructions and proofs within the formal system. The intuition behind this axiom involves understanding the spatial relationships between lines and directions, ensuring that the formal system accurately models geometric reality.

### Dependencies
* `perpdir`
* `pardir`
* `DIRECTION_CLAUSES`
* `BASIS_NONZERO`
* `DIMINDEX_3`
* `ARITH`

### Porting notes
When translating this axiom into other proof assistants, special attention should be given to the handling of geometric predicates like `perpdir` and `pardir`, as well as the representation of basis vectors and dimensional indices. The use of `REWRITE_TAC`, `EXISTS_TAC`, `SIMP_TAC`, and `VEC3_TAC` may have analogs in other systems, but their application and the underlying logic might require adjustments to fit the target system's proof scripting paradigm.

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
* The proof starts by applying `REWRITE_TAC` with `DIRECTION_CLAUSES`, `pardir`, and `perpdir` to transform the goal.
* It then applies `REPEAT STRIP_TAC` to simplify the goal.
* The `SUBGOAL_THEN` tactic is used to prove a subgoal involving `orthogonal` and `cross` properties of vectors.
* The subgoal is proven using `MP_TAC` and then split into two cases using `THENL`.
* In one case, `POP_ASSUM MP_TAC` and `VEC3_TAC` are used to reason about vector properties.
* In the other case, `MESON_TAC` with `CROSS_0` is used to derive a contradiction.

### Mathematical insight
This axiom is related to the concept of direction and orthogonality in 3D space. It states that for any line `l`, there exist two planes `p` and `p'` that are orthogonal to `l` and not parallel to each other. This axiom is likely used to establish properties of lines and planes in 3D geometry.

### Dependencies
* `DIRECTION_CLAUSES`
* `pardir`
* `perpdir`
* `CROSS_0`

### Porting notes
When porting this axiom to another proof assistant, note that the `REWRITE_TAC` and `SUBGOAL_THEN` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `VEC3_TAC` and `MESON_TAC` tactics may require special handling due to their domain-specific reasoning. The `MP_TAC` and `POP_ASSUM MP_TAC` tactics are likely to have direct equivalents in other proof assistants.

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
For all vectors `x`, `a`, and `b` in 3-dimensional real space, if `a` is orthogonal to `x` and `b` is orthogonal to `x` and `a` is not parallel to `b`, then there exists a vector `c` such that `c` is orthogonal to `x` and `a` is not parallel to `c` and `b` is not parallel to `c`.

### Informal sketch
* The proof starts by assuming the premises: `a` is orthogonal to `x`, `b` is orthogonal to `x`, and `a` is not parallel to `b`.
* It then applies `REWRITE_TAC` with `DIRECTION_CLAUSES`, `pardir`, and `perpdir` to rewrite the goals in terms of perpendicular and parallel relations.
* The `REPEAT STRIP_TAC` tactic is used to strip away the universal quantifiers and implications, leaving a more direct statement of the goal.
* The proof then proceeds by exhibiting a specific vector `c`, namely `a + b`, which is claimed to satisfy the required properties.
* The `EXISTS_TAC` tactic is used to introduce this witness, and `POP_ASSUM_LIST(MP_TAC o end_itlist CONJ)` is used to handle the conjunctions in the goal.
* Finally, `VEC3_TAC` is applied to reason about the vector properties in 3-dimensional space.

### Mathematical insight
This theorem provides a way to construct a new vector `c` that is orthogonal to a given vector `x`, given two other vectors `a` and `b` that are also orthogonal to `x` but not parallel to each other. This is useful in geometric and linear algebra contexts where constructing orthogonal vectors is necessary.

### Dependencies
* `DIRECTION_CLAUSES`
* `pardir`
* `perpdir`
* Basic properties of vector addition and orthogonality in 3-dimensional real space

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of vector operations and properties, as different systems may have different libraries or notations for these. Additionally, the `REWRITE_TAC` and `EXISTS_TAC` tactics may need to be replaced with equivalent tactics in the target system, and the `VEC3_TAC` may require a different approach depending on how vectors are represented and reasoned about in the new system.

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
* The proof involves finding suitable points `p`, `p'`, and `p''` that satisfy the given conditions for any line `l`.
* The `MESON_TAC` tactic is used in conjunction with `DIRECTION_AXIOM_4_WEAK` and `ORTHOGONAL_COMBINE` to derive the conclusion.
* The main logical stages include:
  + Establishing the existence of distinct points `p`, `p'`, and `p''`
  + Showing that these points are orthogonal to the line `l`
  + Using the `DIRECTION_AXIOM_4_WEAK` and `ORTHOGONAL_COMBINE` theorems to combine these facts and reach the desired conclusion

### Mathematical insight
This axiom provides a fundamental property of lines and points in a geometric context, ensuring that for any line, there exist distinct points that are orthogonal to it. This is crucial for establishing various geometric and topological results.

### Dependencies
* Theorems:
  + `DIRECTION_AXIOM_4_WEAK`
  + `ORTHOGONAL_COMBINE`

### Porting notes
When translating this axiom into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles existential quantification and orthogonality. The `MESON_TAC` tactic and its underlying logic may need to be replicated or reinterpreted in the target system, potentially involving manual proof steps or tactic scripts that achieve the same logical flow.

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
The `line_tybij` defines a new quotient type named "line" with constructors `mk_line` and destructors `dest_line`, based on the equivalence relation `(||)`.

### Informal sketch
* The definition introduces a new type `line` as a quotient of an existing type, with `mk_line` serving as the constructor and `dest_line` as the destructor.
* The quotient is defined based on the equivalence relation `(||)`, which determines when two elements of the original type are considered equal in the new `line` type.
* This construction is likely used to define lines in a geometric or algebraic context, where the equivalence relation `(||)` captures the idea of two lines being identical.

### Mathematical insight
The `line_tybij` definition provides a way to work with lines in a formal system, allowing for the definition of geometric or algebraic properties and operations on lines. This construction is important for developing theories of geometry, linear algebra, or other areas where lines play a central role.

### Dependencies
* `define_quotient_type`
* `(||)`

### Porting notes
When porting this definition to another proof assistant, attention should be paid to how quotient types are handled. In some systems, quotient types may be defined using different constructs or may require additional proofs of equivalence relations. For example, in Lean, the `quotient` command may be used, while in Coq, the `Equation` module may be relevant. The `(||)` equivalence relation should also be carefully translated, as its definition and properties may be crucial for the correctness of the `line` type.

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
* The proof involves assuming `x || x'` and `y || y'`, which implies certain relationships between the vectors that can be used to show the equivalence of the perpendicularity conditions.
* The `REWRITE_TAC` tactic is used with `perpdir`, `pardir`, and `DIRECTION_CLAUSES` to rewrite the goal in terms of more basic properties of vectors and directions.
* The `VEC3_TAC` tactic is then applied to further simplify and solve the resulting vector equations, leveraging the properties of three-dimensional vectors.

### Mathematical insight
This theorem provides a crucial property about the relationship between parallel vectors and perpendicularity, showing that these geometric relations are preserved under parallelism. This is important in geometric and vector-based proofs, as it allows for the substitution of parallel vectors in arguments about perpendicularity, simplifying many proofs.

### Dependencies
* `perpdir`
* `pardir`
* `DIRECTION_CLAUSES`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how parallelism and perpendicularity are defined and handled, as different systems may have varying levels of support for these concepts. Additionally, the use of `REWRITE_TAC` and `VEC3_TAC` may need to be adapted, as the specific tactics and theorems used for rewriting and solving vector equations can differ significantly between proof assistants.

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
The `perpl` function is defined by lifting the second component of `line_tybij` using the properties `PARDIR_REFL` and `PARDIR_TRANS`, with the name "perpl", and it is well-defined according to `PERPDIR_WELLDEF`.

### Informal sketch
* The definition relies on the `lift_function` mechanism to introduce `perpl` based on the `line_tybij` relation, specifically its second component.
* The properties `PARDIR_REFL` and `PARDIR_TRANS` are used to establish the conditions under which `perpl` is defined, ensuring it respects reflexive and transitive properties.
* The definition is accompanied by a proof `perpl_th` that `perpl` is well-defined, as certified by `PERPDIR_WELLDEF`.

### Mathematical insight
This definition is crucial for introducing a perpendicularity relation (`perpl`) in a geometric or spatial context, leveraging the bijective nature of `line_tybij` and ensuring that the relation adheres to fundamental properties like reflexivity and transitivity, which are essential for any equivalence or order relation.

### Dependencies
#### Theorems and Definitions
* `lift_function`
* `line_tybij`
* `PARDIR_REFL`
* `PARDIR_TRANS`
* `PERPDIR_WELLDEF`

### Porting notes
When translating this definition into another proof assistant, ensure that the equivalent of `lift_function` is used correctly, and that the properties `PARDIR_REFL` and `PARDIR_TRANS` are appropriately applied to validate the well-definedness of `perpl` according to `PERPDIR_WELLDEF`. Special attention should be given to how the target system handles function lifting and the representation of geometric or spatial relations.

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
The theorem `line_lift_thm` is derived by applying the `lift_theorem` function to `line_tybij` with the properties `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS`, using the theorem `perpl_th` as a premise.

### Informal sketch
* The proof involves lifting a theorem `line_tybij` to a higher level using `lift_theorem`.
* The properties `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS` are used to establish the validity of the lifted theorem.
* The `perpl_th` theorem is used as a premise in the lifting process.
* The `lift_theorem` function is used to transfer the theorem `line_tybij` to a new context, preserving its properties.

### Mathematical insight
The `line_lift_thm` theorem is important because it allows the transfer of a theorem about lines to a new context, potentially enabling the application of the theorem in a broader range of situations. The use of `lift_theorem` and the properties `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS` suggests that the theorem is related to the preservation of geometric properties under certain transformations.

### Dependencies
* Theorems: `line_tybij`, `perpl_th`
* Definitions: `lift_theorem`, `PARDIR_REFL`, `PARDIR_SYM`, `PARDIR_TRANS`
* Inductive rules: None

### Porting notes
When translating this theorem to another proof assistant, care should be taken to ensure that the `lift_theorem` function is correctly implemented and that the properties `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS` are properly defined and applied. Additionally, the `perpl_th` theorem should be ported and used as a premise in the lifting process.

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
The axiom `LINE_AXIOM_1` is defined as the result of applying the `line_lift_thm` theorem to `DIRECTION_AXIOM_1`.

### Informal sketch
* The proof or construction of `LINE_AXIOM_1` involves applying the `line_lift_thm` theorem to the `DIRECTION_AXIOM_1` axiom.
* This step likely involves lifting a property or relation defined by `DIRECTION_AXIOM_1` to a line, using the `line_lift_thm` theorem as a foundation.
* The `line_lift_thm` theorem may provide a way to transfer or generalize properties from a lower-dimensional space (e.g., points or directions) to a higher-dimensional space (e.g., lines).

### Mathematical insight
The `LINE_AXIOM_1` axiom is likely a fundamental property or assumption about lines in a geometric or spatial theory. By applying the `line_lift_thm` theorem to `DIRECTION_AXIOM_1`, this axiom establishes a connection between directional properties and linear structures, which may be essential for subsequent theorems or constructions in the theory.

### Dependencies
* Theorems:
	+ `line_lift_thm`
* Axioms:
	+ `DIRECTION_AXIOM_1`

### Porting notes
When translating `LINE_AXIOM_1` to another proof assistant, ensure that the equivalent of `line_lift_thm` is defined and applied correctly. Pay attention to how the target system handles theorem application, axiom definitions, and any relevant type or binding issues. Additionally, verify that the `DIRECTION_AXIOM_1` axiom is properly defined and imported in the target system.

---

## LINE_AXIOM_2

### Name of formal statement
LINE_AXIOM_2

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let LINE_AXIOM_2 = line_lift_thm DIRECTION_AXIOM_2;;
```

### Informal statement
The axiom `LINE_AXIOM_2` is defined as the result of applying the `line_lift_thm` function to `DIRECTION_AXIOM_2`.

### Informal sketch
* The proof or construction of `LINE_AXIOM_2` involves applying the `line_lift_thm` function, which likely lifts a theorem or property related to directions to a line.
* The key step is understanding how `line_lift_thm` transforms `DIRECTION_AXIOM_2` into a statement about lines.
* The process may involve recognizing how directions are related to lines and applying relevant geometric or topological principles.

### Mathematical insight
The `LINE_AXIOM_2` axiom is significant because it establishes a fundamental property or relationship between directions and lines, likely serving as a foundation for further geometric or spatial reasoning. This axiom is important for developing a consistent and comprehensive theory of lines and directions.

### Dependencies
* **Theorems and definitions:**
  * `line_lift_thm`
  * `DIRECTION_AXIOM_2`

### Porting notes
When translating `LINE_AXIOM_2` into another proof assistant, ensure that the equivalent of `line_lift_thm` is correctly defined and applied to the counterpart of `DIRECTION_AXIOM_2`. Pay attention to how directions and lines are represented and related in the target system, as this may involve non-trivial adjustments to capture the intended geometric or topological structure.

---

## LINE_AXIOM_3

### Name of formal statement
LINE_AXIOM_3

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let LINE_AXIOM_3 = line_lift_thm DIRECTION_AXIOM_3;;
```

### Informal statement
The axiom `LINE_AXIOM_3` is defined as the result of applying the `line_lift_thm` theorem to `DIRECTION_AXIOM_3`.

### Informal sketch
* The proof or construction involves applying the `line_lift_thm` to `DIRECTION_AXIOM_3`, which suggests a lifting of a theorem related to direction into a statement about lines.
* The `line_lift_thm` is likely a theorem that generalizes or transforms statements about directions into statements about lines, and `DIRECTION_AXIOM_3` is a fundamental axiom or assumption about directions.
* The main logical stage involves recognizing the applicability of `line_lift_thm` to `DIRECTION_AXIOM_3` and ensuring the resulting statement is well-formed and meaningful in the context of lines.

### Mathematical insight
This axiom is important because it establishes a foundational property or relationship between directions and lines, likely serving as a basis for further theorems or constructions in geometry or a related field. The use of `line_lift_thm` indicates a systematic way of extending or transforming geometric concepts from one domain (directions) to another (lines), highlighting the structured and hierarchical nature of geometric theories.

### Dependencies
- Theorems: `line_lift_thm`
- Axioms: `DIRECTION_AXIOM_3`

### Porting notes
When translating `LINE_AXIOM_3` into another proof assistant, pay attention to how the target system handles the lifting of theorems from one geometric concept to another. Ensure that the equivalent of `line_lift_thm` is appropriately defined and that `DIRECTION_AXIOM_3` is correctly formulated in the new system. Note that differences in how binders or geometric transformations are handled may require adjustments to the ported version of `LINE_AXIOM_3`.

---

## LINE_AXIOM_4

### Name of formal statement
LINE_AXIOM_4

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let LINE_AXIOM_4 = line_lift_thm DIRECTION_AXIOM_4;;
```

### Informal statement
The axiom `LINE_AXIOM_4` is defined as the result of applying the `line_lift_thm` function to `DIRECTION_AXIOM_4`.

### Informal sketch
* The `line_lift_thm` function is applied to `DIRECTION_AXIOM_4` to lift a theorem about directions to a theorem about lines.
* This involves using the `line_lift_thm` function to transform the `DIRECTION_AXIOM_4` axiom into a new axiom that applies to lines.

### Mathematical insight
This axiom is important because it extends a fundamental property of directions to the context of lines, providing a basis for further geometric reasoning.

### Dependencies
* `line_lift_thm`
* `DIRECTION_AXIOM_4` 

### Porting notes
When porting this axiom to another proof assistant, ensure that the equivalent of `line_lift_thm` is defined and applied correctly to the counterpart of `DIRECTION_AXIOM_4`. Note that the specifics of how binders and geometric concepts are handled may vary between systems.

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
Define a new type `point` with constructors `mk_point` and destructors `dest_point`, such that for all `x` of type `line`, a certain property `T` holds, as proven by rewriting using `REWRITE_TAC`.

### Informal sketch
* The definition introduces a new type `point` with two operations: `mk_point` for creating points and `dest_point` for destructing them.
* The `prove` statement ensures that a specific property `T` is true for all `x` of type `line`, utilizing the `REWRITE_TAC` tactic for rewriting.
* The `REWRITE_TAC` tactic is used to discharge the proof obligation by rewriting the goal using existing equalities.

### Mathematical insight
This definition constructs a new type `point` and ensures that it satisfies a certain property `T` for all elements of type `line`. This is likely a foundational step in building a geometric or topological theory, where points are introduced as a basic concept.

### Dependencies
* `line`
* `T`
* `mk_point`
* `dest_point`
* `REWRITE_TAC`

### Porting notes
When translating this definition to another proof assistant, ensure that the equivalent of `new_type_definition` is used, and that the `prove` statement is properly handled, potentially using a similar rewriting tactic. Note that the handling of type definitions and proof obligations may differ between systems, requiring adjustments to the ported code.

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
The predicate `on` is defined such that a point `p` is on a line `l` if and only if the destination point of `p` is perpendicular to `l`.

### Informal sketch
* The definition involves the `perpl` predicate, which checks if a point is perpendicular to a line.
* The `dest_point` function is used to get the destination point of `p`.
* The definition uses a bi-implication (`<=>`) to establish an equivalence between the `on` predicate and the condition involving `perpl` and `dest_point`.

### Mathematical insight
This definition formalizes the geometric concept of a point lying on a line, using the notion of perpendicularity. It is likely used as a foundation for further geometric constructions and theorems.

### Dependencies
* `perpl`
* `dest_point`

### Porting notes
When porting this definition to another proof assistant, ensure that the `perpl` predicate and `dest_point` function are defined and available. Note that the `new_definition` construct may have a direct equivalent in the target system, but the syntax and semantics of the bi-implication and function application may vary.

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
The theorem `POINT_CLAUSES` states that three equivalences hold: 
1. Two points `p` and `p'` are equal if and only if their destinations `dest_point p` and `dest_point p'` are equal.
2. For all points `p`, a property `P` holds for `dest_point p` if and only if `P` holds for all locations `l`.
3. There exists a point `p` such that a property `P` holds for `dest_point p` if and only if there exists a location `l` for which `P` holds.

### Informal sketch
* The proof involves establishing three separate equivalences related to points and their destinations.
* It first considers the equality of points based on their destinations.
* Then, it addresses how a property applies to all points (via their destinations) and how this is equivalent to the property applying to all locations.
* Finally, it examines the existence of points (through their destinations) for which a property holds and shows this is equivalent to the existence of locations with the property.
* The `MESON_TAC` tactic is used in conjunction with `point_tybij`, suggesting a meson-style proof that leverages a bijection property related to points.

### Mathematical insight
This theorem provides foundational equivalences for working with points and their properties, essentially bridging the representation of points with their destinations and locations. It's crucial for establishing a consistent and coherent theory of points and spaces, ensuring that properties and relations defined over points can be meaningfully translated into statements about locations.

### Dependencies
* `point_tybij`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles equality, quantifiers, and bijections. Specifically, the representation of `dest_point` and the property `P` may vary, and the tactic scripts might need adjustments to align with the target system's proof strategies and automation capabilities. Additionally, consider the treatment of locations and how they relate to points, as this may influence the porting of `point_tybij`.

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
The `POINT_TAC` tactic applies the `REWRITE_TAC` tactic with the `on` and `POINT_CLAUSES` theorems to a given theorem `th`, and then applies the `ACCEPT_TAC` tactic to `th`.

### Informal sketch
* The tactic starts with a theorem `th` as input.
* It applies `REWRITE_TAC` to `th` using the `on` and `POINT_CLAUSES` theorems for rewriting.
* After rewriting, it applies `ACCEPT_TAC` to the resulting theorem, effectively accepting it as the next step in a proof.
* The use of `REWRITE_TAC` with specific theorems suggests a simplification or transformation step based on the `POINT_CLAUSES`.

### Mathematical insight
The `POINT_TAC` tactic seems to be designed to simplify or transform theorems involving points, possibly in a geometric or topological context, by applying specific rewrite rules (`POINT_CLAUSES`) and then accepting the result. This could be part of a larger strategy for proving theorems in such domains.

### Dependencies
* `REWRITE_TAC`
* `ACCEPT_TAC`
* `on`
* `POINT_CLAUSES`

### Porting notes
When translating `POINT_TAC` into another proof assistant, pay attention to how rewriting and acceptance tactics are handled. The equivalent of `REWRITE_TAC` and `ACCEPT_TAC` may differ, and the `on` and `POINT_CLAUSES` theorems will need to be defined or imported appropriately in the target system. Additionally, consider how the target system manages tactic composition, as the `THEN` operator is used here to sequence tactics.

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
* The axiom asserts the existence of a unique line passing through two distinct points `p` and `p'`.
* The proof involves assuming the existence of two distinct points and using the `POINT_TAC` tactic to establish the existence of a line passing through them.
* The `LINE_AXIOM_1` tactic is then applied to show that any other line passing through both points must be the same as the original line.
* The key logical stage is the application of the `POINT_TAC` tactic, which allows us to introduce a line passing through the two points.
* The subsequent application of `LINE_AXIOM_1` ensures that this line is unique.

### Mathematical insight
This axiom is a fundamental concept in geometry, ensuring that two distinct points are always collinear and that the line passing through them is unique. This axiom is essential for building more complex geometric structures and theorems.

### Dependencies
* `POINT_TAC`
* `LINE_AXIOM_1`

### Porting notes
When translating this axiom into other proof assistants, care should be taken to ensure that the notion of "on" (i.e., a point lying on a line) is correctly formalized. Additionally, the `POINT_TAC` and `LINE_AXIOM_1` tactics may need to be replaced with equivalent tactics or constructions in the target system.

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
For all lines `l` and `l'`, there exists a point `p` such that `p` lies on `l` and `p` lies on `l'`.

### Informal sketch
* The axiom asserts the existence of a common point for any two lines `l` and `l'`.
* The proof involves applying the `POINT_TAC` tactic, which is likely related to introducing a point that satisfies the given conditions.
* The `LINE_AXIOM_2` term suggests that this axiom is part of a set of foundational assumptions about lines, potentially related to their intersection properties.

### Mathematical insight
This axiom is fundamental in establishing the basic properties of lines and points in a geometric system. It implies that any two lines intersect at some point, which is a crucial assumption in various geometric and topological theories.

### Dependencies
* `POINT_TAC`
* `LINE_AXIOM_2`

### Porting notes
When translating this axiom into other proof assistants, ensure that the concept of a "point on a line" is properly defined and that the existence of a common point for any two lines is adequately expressed. Note that different systems may handle binders and quantifiers slightly differently, so careful attention to the formal structure is necessary.

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
For all points `p`, `p'`, and `p''`, if `p` is not equal to `p'`, `p'` is not equal to `p''`, and `p` is not equal to `p''`, then there does not exist a line `l` such that `p` is on `l`, `p'` is on `l`, and `p''` is on `l`.

### Informal sketch
* The axiom `AXIOM_3` asserts a geometric property about points and lines.
* It assumes three distinct points `p`, `p'`, and `p''`.
* The main logical stage involves showing that these points cannot all lie on the same line `l`.
* This is achieved by using the `POINT_TAC` and `LINE_AXIOM_3` to derive a contradiction or directly prove the non-existence of such a line.

### Mathematical insight
This axiom is fundamental in establishing the basic geometry of points and lines, ensuring that not all points are collinear. It is crucial for building more complex geometric structures and theorems, as it guarantees a level of "non-degeneracy" in geometric configurations.

### Dependencies
* `POINT_TAC`
* `LINE_AXIOM_3`

### Porting notes
When translating this axiom into another proof assistant, ensure that the representation of points, lines, and the "on" relation is correctly defined and used. The axiom's statement relies on the underlying geometry and equality definitions, so these must be accurately ported as well. Note that the `POINT_TAC` and `LINE_AXIOM_3` may not have direct counterparts in other systems, so understanding their roles in the proof (likely related to point and line properties) will be essential for a successful translation.

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
For all lines `l`, there exist three distinct points `p`, `p'`, and `p''` such that `p`, `p'`, and `p''` are on line `l`. The points are distinct in the sense that `p` is not equal to `p'`, `p'` is not equal to `p''`, and `p` is not equal to `p''`.

### Informal sketch
* The axiom asserts the existence of at least three distinct points on any given line `l`.
* The `POINT_TAC` tactic is used to establish this fact, likely by invoking a fundamental property of lines and points, referred to as `LINE_AXIOM_4`.
* The main logical stage involves recognizing that for any line, it is possible to identify three points that satisfy the condition of being distinct from one another.

### Mathematical insight
This axiom is fundamental in establishing the basic properties of geometric objects, specifically lines and points. It ensures that lines have a certain "richness" in terms of the number of points they contain, which is crucial for various geometric constructions and proofs. The intuition behind this axiom is to provide a foundation for more complex geometric reasoning.

### Dependencies
* `LINE_AXIOM_4`
* `POINT_TAC`

### Porting notes
When translating this axiom into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles geometric objects and axioms. Specifically, consider how points and lines are defined and how distinctness of points is expressed. The equivalent of `POINT_TAC` and `LINE_AXIOM_4` will need to be identified or formulated in the target system.

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
The function `projl` is defined as a mapping that takes a vector `x` in R^3 and returns a projective line, where the line is created using the `mk_line` function with a direction given by `mk_dir x`.

### Informal sketch
* The definition involves creating a projective line from a vector in R^3.
* The `mk_dir` function is used to create a direction from the input vector `x`.
* This direction is then used by `mk_line` to create a projective line.
* The `projl` function essentially encapsulates this process, providing a direct way to map vectors to projective lines.

### Mathematical insight
The `projl` function is a fundamental construction in projective geometry, allowing for the representation of lines in a projective space based on vectors in R^3. This definition is crucial for establishing mappings between vectors and geometric objects in projective geometry, facilitating further geometric and algebraic analysis.

### Dependencies
* `mk_line`
* `mk_dir`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how vectors and projective lines are represented. The `mk_dir` and `mk_line` functions may need to be defined or imported from a relevant library, ensuring consistency with the target system's geometric and algebraic foundations. Additionally, consider the handling of types and the potential need for explicit type annotations or coercions to match the source HOL Light definition.

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
The function `projp` is defined such that for any input `x`, `projp x` equals the result of applying `mk_point` to the projection of `x` onto the first component, denoted by `projl x`.

### Informal sketch
* The definition of `projp` involves a composition of functions, starting with the projection of `x` onto its first component using `projl`.
* The result of this projection is then passed to `mk_point`, which constructs a point from the projected value.
* The key logical stage here is understanding how `projl` and `mk_point` interact to define `projp`.
* The definition relies on the existence and properties of `projl` and `mk_point`, which must be defined elsewhere in the theory.

### Mathematical insight
This definition is likely part of a geometric or spatial theory, where points are constructed from projections or components. The `projp` function serves to create a point based on the first component of an input, which could be useful in various geometric transformations or analyses. Understanding this definition requires familiarity with the concepts of projection and point construction in the context of the broader theory.

### Dependencies
#### Definitions
* `projl`
* `mk_point`
#### Theorems or Axioms
None explicitly mentioned, but the definition assumes the existence and certain properties of `projl` and `mk_point`.

### Porting notes
When translating this definition into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how these systems handle function definitions, especially those involving compositions and projections. Ensure that equivalent definitions for `projl` and `mk_point` exist in the target system and that their properties are established, as these are crucial for the correctness of `projp`. Additionally, consider the potential need to explicitly state or prove theorems about the behavior of `projp` that might be implicit or automatically derived in HOL Light.

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
For all lines `l`, there exists a vector `x` not equal to the zero vector, such that `l` is equal to the projection of `x` onto the line.

### Informal sketch
* The proof starts by considering an arbitrary line `l`.
* It then assumes the existence of a direction `d` such that `l` can be represented as a line defined by `d`.
* Using `MESON_TAC` with `fst line_tybij` and `snd line_tybij`, it establishes a relationship between `l` and `d`.
* The proof then uses `REWRITE_TAC` with `projl` to express the projection of a vector onto `l` in terms of `d`.
* By applying `EXISTS_TAC` with `dest_dir d`, it shows that there exists a vector `x` (derived from `d`) that satisfies the condition `l = projl x`.
* Finally, `MESON_TAC` with `direction_tybij` is used to establish the desired property.

### Mathematical insight
This theorem provides a way to relate lines to vectors in a geometric context, specifically showing that any line can be associated with a non-zero vector through the projection operation. This is a fundamental connection in geometric and vector space theories.

### Dependencies
* Theorems:
  * `fst line_tybij`
  * `snd line_tybij`
  * `direction_tybij`
* Definitions:
  * `projl`
  * `mk_line`
  * `dest_dir`

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to the handling of vectors, lines, and projections, as different systems may represent these concepts differently. Additionally, the use of `MESON_TAC` and `REWRITE_TAC` tactics may need to be adapted to the target system's tactics and rewriting mechanisms.

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
The formal statement introduces a new specification named `homol`, which is defined using the `new_specification` construct. This specification involves applying the `REWRITE_RULE` tactic with the `SKOLEM_THM` theorem to the `PROJL_TOTAL` term.

### Informal sketch
* The definition of `homol` relies on applying the `REWRITE_RULE` tactic to transform `PROJL_TOTAL` using the `SKOLEM_THM` theorem.
* The `SKOLEM_THM` theorem is likely involved in handling existential quantification or Skolemization.
* The `PROJL_TOTAL` term is the subject of this transformation, possibly representing a total projection or a related concept.
* The overall goal is to create a new specification that captures a specific property or relationship, as defined by the resulting expression after applying the rewrite rule.

### Mathematical insight
The `homol` specification seems to be part of a larger development involving projections and possibly Skolem functions, which are used to eliminate existential quantifiers. This construction is important for handling or transforming expressions involving total projections in a way that is consistent with the underlying mathematical theory.

### Dependencies
* Theorems:
  + `SKOLEM_THM`
* Definitions or constants:
  + `PROJL_TOTAL`
  + `new_specification`
  + `REWRITE_RULE`

### Porting notes
When translating this item into another proof assistant, special attention should be given to how Skolemization and existential quantification are handled, as well as how rewrite rules are applied. The equivalent of `REWRITE_RULE` and the `SKOLEM_THM` theorem must be identified in the target system. Additionally, ensure that the `new_specification` construct has a direct analogue or can be appropriately simulated in the target proof assistant.

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
* The proof starts by assuming an arbitrary `p`.
* It then applies the definition of `projp` to rewrite `p` in terms of `x`.
* Using the `REWRITE_TAC` tactic with the `projp` definition, it transforms the goal into a form where `MESON_TAC` can be applied.
* `MESON_TAC` is used with the theorems `PROJL_TOTAL` and `point_tybij` to derive the existence of a non-zero `x` that satisfies the condition `p = projp x`.
* The `point_tybij` theorem likely provides a bijection property that helps in establishing the relationship between `p` and `x`.

### Mathematical insight
This theorem establishes a fundamental property about projections, showing that every `p` can be represented as the projection of some non-zero vector `x`. This is crucial in understanding the behavior of projections and their relationship with the underlying vector space. The use of `PROJL_TOTAL` and `point_tybij` suggests that this theorem is built upon a foundation of linear algebra and potentially a specific representation of points or vectors.

### Dependencies
* Theorems:
  - `PROJL_TOTAL`
  - `point_tybij`
* Definitions:
  - `projp`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how projections are defined and how the `REWRITE_TAC` and `MESON_TAC` tactics are handled, as these may have direct analogs or require manual replication of their functionality. Additionally, ensuring that the `PROJL_TOTAL` and `point_tybij` theorems (or their equivalents) are properly established and accessible in the target system is crucial for a successful port.

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
The function `homop` is defined as the composition of `homol` with `dest_point`, applied to an input `p`. In other words, `homop` of `p` equals `homol` of the destination point of `p`.

### Informal sketch
* The definition of `homop` relies on applying the `homol` function to the result of `dest_point` applied to `p`.
* This implies that `homop` acts on an input `p` by first extracting its destination point via `dest_point`, and then applying `homol` to this point.
* The key logical step involves function composition, where `homop` is essentially a new function that sequences these two operations.

### Mathematical insight
The definition of `homop` suggests it plays a role in a geometric or topological context, possibly relating to homology or homotopy theory, given the names `homol` and `homop`. The `dest_point` function implies a notion of direction or endpoint, which `homop` then further transforms. This construction might be crucial in establishing properties or theorems about these geometric or topological objects.

### Dependencies
- Definitions: `homol`, `dest_point`
- Theorems or axioms: None explicitly mentioned, but potentially `homol` and `dest_point` rely on other definitions or theorems not listed here.

### Porting notes
When translating `homop_def` into another proof assistant, ensure that the equivalent of `new_definition` is used, and that `homol` and `dest_point` are correctly defined or imported. Pay attention to how function composition is handled, as this might differ between systems. Additionally, consider the types of `p`, `homol`, and `dest_point` to ensure compatibility and accurate translation of the definition.

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
For all points `p`, it is not the case that `homop p` equals the zero vector, and `p` equals the projection of `homop p`. This statement involves a universal quantifier over points `p`, asserting a conjunction of two properties for each `p`.

### Informal sketch
* The proof begins by generalizing over all points `p` using `GEN_TAC`.
* It then applies `REWRITE_TAC` to rewrite the statement using the definitions of `homop`, `projp`, and a `MESON` rule derived from `point_tybij`, which relates points and their representations.
* The `MESON` rule is used with a specific lemma `p = mk_point l <=> dest_point p = l` to establish a crucial equivalence.
* Finally, `MATCH_ACCEPT_TAC homol` is applied to complete the proof, presumably by matching the rewritten statement with a known lemma or axiom `homol`.

### Mathematical insight
This theorem establishes a fundamental property relating the `homop` function, which presumably performs some kind of homogeneous operation on points, and the `projp` function, which projects points. The theorem ensures that for any point `p`, applying `homop` and then `projp` returns `p` itself, provided that `homop p` is not the zero vector. This suggests that `homop` preserves certain geometric properties of points under projection, which is crucial in geometric and algebraic reasoning.

### Dependencies
* **Definitions:**
  - `homop`
  - `projp`
  - `point_tybij`
* **Theorems/Lemmas:**
  - `homol`
* **Inductive Rules:**
  None

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to the handling of the `GEN_TAC` and `REWRITE_TAC` tactics, as well as the `MESON` rule, which might not have direct counterparts. Additionally, the representation of points and vectors, and the specific definitions of `homop` and `projp`, will need to be carefully aligned with the target system's libraries and notations.

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
* The definition of `parallel` is based on the property that the cross product of two parallel vectors is the zero vector.
* To prove that two vectors are parallel, one would need to show that their cross product is zero.
* The definition uses the `cross` operator and the `vec 0` constant, which represents the zero vector.

### Mathematical insight
The `parallel` relation is a fundamental concept in geometry and linear algebra, as it captures the idea of two vectors having the same direction or being parallel to each other. This definition is important because it provides a way to formalize and reason about parallelism in a mathematical framework.

### Dependencies
* `cross`
* `vec 0`

### Porting notes
When translating this definition to other proof assistants, note that the `cross` operator and the `vec 0` constant may need to be defined or imported from a relevant library. Additionally, the syntax for defining a new relation may differ between systems, so care should be taken to ensure that the definition is translated correctly.

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
* The proof begins by introducing universal quantifiers for `p` and `l` using `GEN_TAC`.
* It then applies `GEN_REWRITE_TAC` with `homop` and `homol` to rewrite the terms involving `p` and `l`.
* Next, it uses `REWRITE_TAC` to apply several definitions and theorems, including `on`, `projp`, `projl`, `point_tybij`, `perpl_th`, and `perpdir`, to simplify the expression.
* The `BINOP_TAC` is then applied, likely to handle the biconditional.
* Finally, `MESON_TAC` is used with `homol`, `homop`, and `direction_tybij` to derive the conclusion.

### Mathematical insight
This theorem provides a relationship between a point being on a line and the orthogonality of their respective homogeneous representations. It's crucial for establishing connections between geometric and algebraic properties in the context of projective geometry.

### Dependencies
#### Theorems and definitions
* `homop`
* `homol`
* `on`
* `projp`
* `projl`
* `point_tybij`
* `perpl_th`
* `perpdir`
* `direction_tybij`

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles universal quantification, term rewriting, and the application of theorems. Specifically, the equivalents of `GEN_REWRITE_TAC`, `REWRITE_TAC`, and `MESON_TAC` will need to be identified and applied appropriately. Additionally, ensure that the definitions of `homop`, `homol`, and other used terms are correctly ported, as their representations may vary between systems.

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
* The proof starts by assuming two arbitrary lines `l` and `l'`.
* It then applies a series of rewrites using `GEN_REWRITE_TAC` to simplify the expression involving `homol`, `projl`, and `mk_line`.
* The `MESON` tactic is used to derive a key equivalence involving `line_tybij`, `fst`, and `snd`.
* Further rewrites are applied using `REWRITE_TAC` with `PARDIR_EQUIV`, `pardir`, and `parallel` to transform the expression into a form that can be directly compared.
* The final step uses `MESON_TAC` with `homol` and `direction_tybij` to establish the desired equivalence.

### Mathematical insight
This theorem provides a condition for when two lines are equal based on the parallelism of their homologies. It is a fundamental result in the theory of lines and their geometric properties, highlighting the relationship between line equality and the parallelism of their homologies.

### Dependencies
* `homol`
* `parallel`
* `projl`
* `mk_line`
* `line_tybij`
* `PARDIR_EQUIV`
* `pardir`
* `direction_tybij`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to the handling of `GEN_REWRITE_TAC` and `MESON_TAC`, as these may have different counterparts or require manual unfolding. Additionally, ensure that the definitions of `homol`, `parallel`, and other dependencies are correctly ported, as their properties are crucial to the proof.

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
* The proof involves showing a bi-implication between the equality of `p` and `p'` and the parallelism of `homop p` and `homop p'`.
* The `REWRITE_TAC` tactic is used with `homop_def` and `GSYM EQ_HOMOL` to rewrite the goal, likely simplifying or transforming the expressions involving `homop`.
* The `MESON_TAC` tactic with `point_tybij` is then applied to deduce the conclusion, possibly using properties of points or bijective functions to establish the parallelism condition.
* Key steps involve understanding the definition of `homop`, the relationship between equality and parallelism, and how `point_tybij` supports the deduction.

### Mathematical insight
This theorem provides a condition for when two entities `p` and `p'` are equal, based on the parallelism of their images under the `homop` function. It suggests a deep connection between the equality of objects and the geometric or structural relationship of their transformations under `homop`, highlighting the importance of this function in preserving or reflecting the original structure.

### Dependencies
#### Theorems and Definitions
* `homop_def`
* `EQ_HOMOL`
* `point_tybij`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how the `homop` function is defined and how parallelism is represented. The `REWRITE_TAC` and `MESON_TAC` tactics may have direct analogs in other systems, but the specific handling of equality, bi-implications, and geometric properties like parallelism could vary, requiring careful adaptation. Additionally, ensure that the `point_tybij` property is appropriately translated or proved in the target system, as it seems crucial for the deduction.

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
* It then proceeds by cases, depending on whether `x` is equal to the zero vector in `real^3`.
* In the case where `x` is not the zero vector, the proof involves rewriting using `CROSS_0` and applying the `homol` property to `projl x`.
* The proof then involves a series of rewrites and applications of various properties, including `projl`, `dest_line`, `PARDIR_EQUIV`, `pardir`, and `direction_tybij`.
* The key steps involve manipulating the expressions to show the desired parallelism relationship.

### Mathematical insight
This theorem provides a well-definedness result for the homogeneous coordinate map, specifically showing that any vector `x` is parallel to its image under the composition of `homol` and `projl`. This result is likely important for establishing the consistency and correctness of geometric constructions involving homogeneous coordinates.

### Dependencies
* Theorems:
  + `parallel`
  + `homol`
  + `projl`
  + `CROSS_0`
  + `PARDIR_EQUIV`
  + `pardir`
  + `direction_tybij`
* Definitions:
  + `projl`
  + `homol`
  + `parallel`
  + `dest_line`
  + `line_tybij`

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of vector operations and geometric properties. The `GEN_TAC` and `ASM_CASES_TAC` tactics may need to be replaced with equivalent constructs in the target system. Additionally, the `REWRITE_TAC` and `ASM_REWRITE_TAC` tactics may require manual rewriting or the use of equivalent simplification tactics in the target system.

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
For all `x`, `x` is parallel to the homography of the projection of `x`. This statement involves a universal quantifier and asserts a geometric relationship between `x` and a transformation of its projection.

### Informal sketch
* The proof begins with the goal of showing `!x. parallel x (homop(projp x))`, which involves a universal quantification over `x`.
* The first step involves rewriting using `homop_def`, `projp`, and `REWRITE_RULE[] point_tybij`, which suggests applying definitions and potentially simplifying types or properties related to points and their transformations.
* The next step involves another rewriting using `PARALLEL_PROJL_HOMOL`, indicating a connection to properties of parallelism and homologies of projections.
* The sequence of rewrites suggests that the proof leverages previously established relationships between geometric transformations and properties to establish the parallelism condition for all `x`.

### Mathematical insight
This theorem appears to establish a fundamental property relating geometric objects and their transformations under projection and homography. It suggests that for any `x`, applying a homography to its projection results in a figure that is parallel to `x`. This kind of property is crucial in geometric and projective geometry, where understanding how transformations preserve or alter geometric relationships is essential.

### Dependencies
- Theorems:
  - `PARALLEL_PROJL_HOMOL`
- Definitions:
  - `homop`
  - `projp`
  - `point_tybij`
- Other:
  - `parallel`
  - `homography` and `projection` concepts

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how universal quantification and geometric predicates are handled. The `REWRITE_TAC` and `REWRITE_RULE` tactics in HOL Light are used for simplification and applying equalities, which may have direct counterparts in other systems (e.g., `rewrite` in Lean, `rewrite` tactic in Coq). Understanding the equivalent of `homop`, `projp`, and `point_tybij` in the target system, as well as how parallelism is defined, will be crucial for a successful port.

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
For all vectors `x`, if `x` is not the zero vector, then there exists a scalar `a` not equal to zero such that the homogenous projection of `x` is equal to `a` times `x`.

### Informal sketch
* The proof starts by assuming `x` is not the zero vector.
* It then proceeds to show the existence of a non-zero scalar `a` that satisfies the equation `homop(projp x) = a % x`.
* The proof uses cases to handle the possibility of `x` being the zero vector and `c` being zero.
* Key steps involve applying `MP_TAC`, `MATCH_MP_TAC`, and `ASM_REWRITE_TAC` to manipulate the terms and use relevant lemmas such as `PARALLEL_PROJP_HOMOP`, `MONO_FORALL`, `parallel`, `CROSS_EQ_0`, and `COLLINEAR_LEMMA`.
* The `GEN_TAC` and `X_GEN_TAC` are used to introduce new variables and `ASM_CASES_TAC` is used to handle different cases.

### Mathematical insight
This theorem provides insight into the properties of homogeneous projections of vectors, specifically how they relate to scalar multiplication. It is a foundational result in understanding geometric transformations and projections, showing that under certain conditions, a homogeneous projection can be represented as a scaling of the original vector.

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
When translating this theorem into other proof assistants, pay special attention to how each system handles vector operations, homogeneous projections, and scalar multiplication. The use of `GEN_TAC` and `X_GEN_TAC` for introducing variables and `ASM_CASES_TAC` for case analysis may need to be adapted based on the target system's tactic language. Additionally, the `MATCH_MP_TAC` and `ASM_REWRITE_TAC` tactics might have direct equivalents or require more manual manipulation in other systems.

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
The `bracket` function is defined as the determinant of a vector formed by the `homop` of three arguments `a`, `b`, and `c`.

### Informal sketch
* The definition involves calculating the determinant of a vector that results from applying the `homop` operation to each of the input arguments `a`, `b`, and `c`.
* The `homop` operation is presumably defined elsewhere and is applied to each argument individually.
* The resulting values are then used to construct a vector, for which the determinant is computed.
* The determinant calculation is the core of the `bracket` function's definition, implying a relationship with linear algebraic concepts.

### Mathematical insight
The `bracket` function seems to be related to the concept of brackets in algebra, potentially in the context of Grassmann algebra or exterior algebra, where brackets are used to denote certain operations on vectors. The use of determinants and the `homop` operation suggests a connection to geometric or algebraic structures.

### Dependencies
* `det` (determinant function)
* `vector` (vector construction function)
* `homop` (operation applied to each argument)

### Porting notes
When translating this definition into another proof assistant, ensure that the equivalent of `homop` and `det` functions are defined and accessible. Additionally, verify that vector construction and determinant calculations are handled similarly. Pay attention to the specific implementation of `homop`, as its definition is crucial for the correctness of the `bracket` function.

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
The set `s` is collinear if and only if there exists a line `l` such that for all points `p`, if `p` is an element of `s`, then `p` lies on `l`.

### Informal sketch
* The definition of `COLLINEAR` involves an existential quantification over lines `l`.
* For a given set `s` to be considered collinear, we must be able to find at least one line `l` that satisfies the condition.
* The condition itself involves a universal quantification over points `p` in `s`, stating that every point `p` in `s` must lie on the line `l`.
* The `on` relation denotes that a point lies on a line, which is a primitive or defined relation in the context of this formal system.

### Mathematical insight
The concept of `COLLINEAR` is fundamental in geometry, capturing the idea that a set of points is collinear if they all lie on the same line. This definition is crucial for establishing various geometric properties and theorems, as it provides a clear criterion for determining when points are aligned.

### Dependencies
* `on` 
* Possibly: definitions or axioms related to points, lines, and set membership (`IN`)

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, ensure that the existential and universal quantifiers are correctly represented. Also, verify that the `on` relation is appropriately defined or axiomatized in the target system. Note that differences in how these systems handle binders, quantifiers, and geometric primitives may require adjustments to the translation.

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
  MESON_TAC[AXIOM_1; AXIOM_3]);;
```

### Informal statement
For all `a`, the set containing only `a` is collinear.

### Informal sketch
* The proof starts with the assumption that `a` is an arbitrary element.
* It then applies the definition of `COLLINEAR` and rewrites the statement using `FORALL_IN_INSERT` and `NOT_IN_EMPTY`.
* The `MESON_TAC` tactic is used to derive the conclusion from `AXIOM_1` and `AXIOM_3`.
* The key idea is to show that a singleton set satisfies the conditions for being collinear, leveraging the given axioms.

### Mathematical insight
This statement is important because it establishes a basic property of collinearity, namely that a single point is always collinear. This is a foundational result that can be used to build more complex geometric constructions and theorems.

### Dependencies
#### Theorems and definitions
* `COLLINEAR`
* `FORALL_IN_INSERT`
* `NOT_IN_EMPTY`
* `AXIOM_1`
* `AXIOM_3`

### Porting notes
When translating this theorem into another proof assistant, ensure that the equivalent of `MESON_TAC` is used to apply the relevant axioms (`AXIOM_1` and `AXIOM_3`) in the context of the `COLLINEAR` definition. Pay attention to how the target system handles rewriting and tactic application, as direct translation of HOL Light tactics may not be possible.

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
  ASM_MESON_TAC[AXIOM_1])
```

### Informal statement
For all points `a` and `b`, the set `{a, b}` is collinear.

### Informal sketch
* The proof begins by considering the case where `a` equals `b`, and then proceeds to handle the case where `a` and `b` are distinct.
* The `ASM_CASES_TAC` tactic is used to perform case analysis on whether `a` equals `b`.
* The `ASM_REWRITE_TAC` tactic is applied with `INSERT_AC` and `COLLINEAR_SINGLETON` to rewrite the statement.
* The `REWRITE_TAC` tactic is then used with `COLLINEAR`, `FORALL_IN_INSERT`, and `NOT_IN_EMPTY` to further simplify the statement.
* Finally, the `ASM_MESON_TAC` tactic is used with `AXIOM_1` to complete the proof.

### Mathematical insight
This theorem states that any set containing two points is collinear, which is a fundamental property in geometry. The proof relies on the definition of collinearity and basic set theory principles.

### Dependencies
* Theorems:
  * `AXIOM_1`
* Definitions:
  * `COLLINEAR`
  * `COLLINEAR_SINGLETON`
  * `INSERT_AC`
  * `FORALL_IN_INSERT`
  * `NOT_IN_EMPTY`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of case analysis and rewriting tactics, as these may differ between systems. Additionally, ensure that the `COLLINEAR` definition and related theorems are properly ported, as they are crucial to the proof.

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
For all points `a`, `b`, and `c`, the points are collinear if and only if there exists a line `l` such that `a` is on `l`, `b` is on `l`, and `c` is on `l`.

### Informal sketch
* The theorem `COLLINEAR_TRIPLE` establishes an equivalence between the `COLLINEAR` relation among three points and the existence of a line passing through these points.
* The proof involves rewriting the `COLLINEAR` definition using the `REWRITE_TAC` tactic, which applies the definitions of `COLLINEAR`, `FORALL_IN_INSERT`, and `NOT_IN_EMPTY` to transform the statement into a more manageable form.
* Key steps include:
  + Expressing the `COLLINEAR` relation in terms of the existence of a common line.
  + Applying the `FORALL_IN_INSERT` and `NOT_IN_EMPTY` properties to handle the universal and existential quantifiers.

### Mathematical insight
The `COLLINEAR_TRIPLE` theorem provides a fundamental characterization of collinearity in terms of the geometric concept of a line. This theorem is crucial for establishing various geometric properties and theorems that rely on the notion of collinearity.

### Dependencies
* Theorems:
  + `COLLINEAR`
* Definitions:
  + `FORALL_IN_INSERT`
  + `NOT_IN_EMPTY`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles existential quantification and line definitions. Specifically, ensure that the `COLLINEAR` relation and line existence are properly aligned with the target system's geometric primitives and quantifier handling mechanisms.

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
For all points `p1`, `p2`, and `p3`, the set `{p1, p2, p3}` is collinear if and only if the bracket of `p1`, `p2`, and `p3` equals the zero vector.

### Informal sketch
* The proof involves showing the equivalence between the collinearity of three points and the bracket of these points being zero.
* It first proves a lemma stating that if `x` and `y` are vectors such that `x cross y = vec 0` and `x` is not the zero vector, and `a`, `b`, and `c` are orthogonal to `x`, then they are also orthogonal to `y`.
* The main proof uses this lemma and involves cases, including when `p1` equals `p2`, and when they are distinct.
* It employs various tactics such as `REWRITE_TAC`, `MATCH_MP_TAC`, and `EXISTS_TAC` to manipulate the expressions and apply relevant theorems.
* Key steps include rewriting expressions using `COLLINEAR_TRIPLE`, `bracket`, and `ON_HOMOL`, and using `MONO_FORALL` and `CONJUNCT1` to manipulate the quantifiers and implications.

### Mathematical insight
This theorem provides a geometric condition for the collinearity of three points in terms of the bracket operation, which is a fundamental concept in geometric algebra and projective geometry. The bracket of three points can be seen as a measure of their linear dependence, and this theorem shows that they are collinear if and only if their bracket is zero.

### Dependencies
* Theorems:
  + `homol`
  + `MONO_FORALL`
  + `LEFT_IMP_EXISTS_THM`
* Definitions:
  + `COLLINEAR`
  + `bracket`
  + `ON_HOMOL`
  + `orthogonal`
  + `cross`
  + `vec`
  + `mk_line`
  + `mk_dir`
  + `homop`
* Other:
  + `REAL_RING` theory for real numbers
  + `VEC3_TAC` for vector operations

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of vectors, the `cross` product, and the `bracket` operation. The `orthogonal` relation and the `homop` function may also require special care. The use of `REWRITE_TAC` and `MATCH_MP_TAC` suggests that the target system should support similar rewriting and pattern matching capabilities. Additionally, the `EXISTS_TAC` and `CONJUNCT1` tactics imply the need for existential quantification and conjunction handling.

---

## BRACKET_SWAP,BRACKET_SHUFFLE

### Name of formal statement
BRACKET_SWAP,BRACKET_SHUFFLE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BRACKET_SWAP,BRACKET_SHUFFLE = (CONJ_PAIR o prove)
 (`bracket[x;y;z] = --bracket[x;z;y] /\
   bracket[x;y;z] = bracket[y;z;x] /\
   bracket[x;y;z] = bracket[z;x;y]`,
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING)
```

### Informal statement
The theorem `BRACKET_SWAP,BRACKET_SHUFFLE` asserts that for any `x`, `y`, and `z`, the following equalities hold: 
- `bracket[x;y;z]` is equal to `--bracket[x;z;y]`, 
- `bracket[x;y;z]` is equal to `bracket[y;z;x]`, and 
- `bracket[x;y;z]` is equal to `bracket[z;x;y]`.

### Informal sketch
* The proof starts by applying `CONJ_PAIR` to prove the conjunction of the three equalities.
* The `prove` function is used with a tactic that first applies `REWRITE_TAC` with the `bracket`, `DET_3`, and `VECTOR_3` theorems to rewrite the expressions.
* Then, it applies `CONV_TAC REAL_RING` to convert the expressions using the `REAL_RING` theory.
* The main logical stages involve rewriting and simplifying the expressions using the given theorems and then converting them to a suitable form.

### Mathematical insight
This theorem provides a way to shuffle the arguments of the `bracket` function into a canonical order, which can be useful for simplifying expressions and proving other theorems. The `bracket` function is likely related to the scalar triple product or a similar concept, and this theorem helps to establish its symmetry properties.

### Dependencies
* Theorems: `bracket`, `DET_3`, `VECTOR_3`
* Tactics: `REWRITE_TAC`, `CONV_TAC`
* Theory: `REAL_RING`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of the `bracket` function and its properties. The `REWRITE_TAC` and `CONV_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `REAL_RING` theory may need to be replaced with a similar theory or set of axioms in the target system.

---

## BRACKET_SWAP_CONV

### Name of formal statement
BRACKET_SWAP_CONV

### Type of the formal statement
Theorem/conversion

### Formal Content
```ocaml
let BRACKET_SWAP_CONV =
  let conv = GEN_REWRITE_CONV I [BRACKET_SWAP] in
  fun tm -> let th = conv tm in
            let tm' = rand(rand(concl th)) in
            if term_order tm tm' then th else failwith "BRACKET_SWAP_CONV"
```

### Informal statement
This conversion `BRACKET_SWAP_CONV` applies a rewrite rule `BRACKET_SWAP` to a given term `tm` using `GEN_REWRITE_CONV` with the identity context `I`, resulting in a theorem `th`. It then checks if the term `tm'`, which is the right-hand side of the conclusion of `th`, is less than the original term `tm` according to `term_order`. If so, it returns the theorem `th`; otherwise, it fails with an error message.

### Informal sketch
* Apply `GEN_REWRITE_CONV` with the `BRACKET_SWAP` rule to the input term `tm` to obtain a theorem `th`.
* Extract the right-hand side of the conclusion of `th`, denoted as `tm'`.
* Compare `tm` and `tm'` using `term_order` to determine if the conversion has resulted in a "smaller" term.
* If `tm'` is "smaller" than `tm`, return the theorem `th` as the result of the conversion; otherwise, indicate failure.

### Mathematical insight
The `BRACKET_SWAP_CONV` conversion appears to be designed to apply a specific rewrite rule `BRACKET_SWAP` to terms, potentially simplifying or rearranging them. The use of `term_order` to compare the original and resulting terms suggests an interest in ensuring that the conversion leads to a term that is in some sense "smaller" or more normalized, which can be useful in proof search or simplification processes.

### Dependencies
* `GEN_REWRITE_CONV`
* `BRACKET_SWAP`
* `I` (identity context)
* `term_order`

### Porting notes
When translating this conversion into another proof assistant, special attention should be paid to how rewrite rules and term orderings are handled. The equivalent of `GEN_REWRITE_CONV` and the `term_order` function may need to be identified or implemented in the target system. Additionally, the `BRACKET_SWAP` rule will need to be defined or imported in the new context. Differences in how terms are represented and compared (e.g., using `term_order`) may require adjustments to the condition for returning the theorem or indicating failure.

---

## DESARGUES_DIRECT

### Name of formal statement
DESARGUES_DIRECT

### Type of the formal statement
Theorem

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
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING)
```

### Informal statement
The theorem `DESARGUES_DIRECT` states that given a set of non-collinear points `A'`, `B`, `S`, `A`, `P`, `C`, `R`, `C'`, `B'`, and `Q` satisfying certain conditions, if `P`, `A'`, `A` are collinear, `P`, `B`, `B'` are collinear, `P`, `C'`, `C` are collinear, `B`, `C`, `Q` are collinear, `B'`, `C'`, `Q` are collinear, `A`, `R`, `C` are collinear, `A'`, `C'`, `R` are collinear, `B`, `S`, `A` are collinear, and `A'`, `S`, `B'` are collinear, then `Q`, `S`, `R` are collinear.

### Informal sketch
* The proof starts with a set of assumptions about non-collinear points and applies the `COLLINEAR_BRACKET` definition.
* It then uses `SUBGOAL_THEN` to apply several implications involving `bracket` expressions.
* The proof proceeds with a series of applications of `MATCH_MP_TAC`, `DISCH_THEN`, and `REWRITE_TAC` to manipulate the expressions and apply properties of real numbers.
* Key steps involve using `BRACKET_SHUFFLE` and `BRACKET_SWAP_CONV` to rearrange terms and apply properties of determinants and vectors.
* The proof concludes with an application of `MATCH_MP_TAC` to establish the final collinearity condition.

### Mathematical insight
The `DESARGUES_DIRECT` theorem is a direct proof of Desargues' theorem, which is a fundamental result in projective geometry. The theorem states that if two triangles are perspective from a point, then they are also perspective from a line. The proof involves a series of algebraic manipulations using `bracket` expressions, which represent determinants of vectors. The theorem is important in projective geometry and has applications in various fields, including computer vision and graphics.

### Dependencies
* `COLLINEAR_BRACKET`
* `bracket`
* `DET_3`
* `VECTOR_3`
* `REAL_RING`
* `BRACKET_SHUFFLE`
* `BRACKET_SWAP_CONV`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `bracket` expressions and `COLLINEAR_BRACKET` definition are properly translated. Additionally, the use of `SUBGOAL_THEN` and `MATCH_MP_TAC` may require careful handling, as these tactics may not have direct equivalents in other proof assistants. The `REAL_RING` and `BRACKET_SHUFFLE` properties may also require special attention, as they involve specific properties of real numbers and determinants.

---

