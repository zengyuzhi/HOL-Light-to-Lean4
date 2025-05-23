# polyhedron.ml

## Overview

Number of statements: 58

The `polyhedron.ml` file formalizes Jim Lawrence's proof of Euler's relation, a fundamental concept in geometry and topology. It builds upon imports from `polytope`, `binomial`, `inclusion_exclusion`, and `combinations` to establish key definitions and theorems. The file's purpose is to provide a formal proof of Euler's relation, which relates the number of vertices, edges, and faces of a polyhedron. This formalization contributes to the larger library by providing a rigorous foundation for geometric and topological reasoning.

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
The `hyperplane_side` function determines the side of a hyperplane that a point is on. It takes a pair `(a, b)` representing the hyperplane equation `a dot x - b = 0` and a point `x` in `real^N` space, and returns the real sign of the expression `a dot x - b`, indicating the side of the hyperplane on which the point lies.

### Informal sketch
* The definition uses the `real_sgn` function to determine the sign of the expression `a dot x - b`, which represents the difference between the dot product of `a` and `x` and the constant term `b`.
* The `dot` operator represents the dot product of two vectors.
* The `real_sgn` function returns a value indicating the sign of its input, which in this case determines the side of the hyperplane on which the point `x` lies.

### Mathematical insight
The `hyperplane_side` function is a key concept in geometry and linear algebra, as it allows for the classification of points in space relative to a hyperplane. The function is important in various applications, including computer graphics, machine learning, and computational geometry.

### Dependencies
* `real_sgn`
* `dot`
* `Multivariate/polytope.ml`
* `Library/binomial.ml`
* `100/inclusion_exclusion.ml`
* `100/combinations.ml`

### Porting notes
When porting this definition to other proof assistants, note that the `real_sgn` function and the `dot` operator may need to be defined or imported separately. Additionally, the `real^N` type may need to be represented differently, depending on the target system's support for vector spaces and real numbers.

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
The relation `hyperplane_equiv` between two points `x` and `y` with respect to a set of hyperplanes `A` holds if and only if for all hyperplanes `h` in `A`, the sides of `h` on which `x` and `y` lie are the same.

### Informal sketch
* The definition involves a universal quantification over all hyperplanes `h` in the set `A`.
* For each hyperplane `h`, it checks if the `hyperplane_side` function returns the same value for points `x` and `y`.
* This essentially means that `x` and `y` are on the same side of every hyperplane in `A`.
* The `hyperplane_side` function is crucial here, as it determines the side of a hyperplane on which a point lies.

### Mathematical insight
The `hyperplane_equiv` relation imposes an equivalence relation on points based on their positions relative to a set of hyperplanes. This is important in geometric and topological contexts, where the arrangement of hyperplanes can partition the space into distinct regions. The relation captures the idea that two points are equivalent if they cannot be separated by any hyperplane in the arrangement.

### Dependencies
* `hyperplane_side`

### Porting notes
When translating this definition into another proof assistant, ensure that the `hyperplane_side` function is correctly defined and that the universal quantification over hyperplanes in `A` is properly handled. Note that the representation of sets and functions may differ between systems, so careful attention to these details is necessary. Additionally, the use of `new_definition` in HOL Light may correspond to different constructs in other systems (e.g., `Definition` in Coq or `definition` in Isabelle).

---

## HYPERPLANE_EQUIV_REFL

### Name of formal statement
HYPERPLANE_EQUIV_REFL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_REFL = prove
 (`!A x. hyperplane_equiv A x x`,
  REWRITE_TAC[hyperplane_equiv]);;
```

### Informal statement
For all sets A and all elements x, it holds that x is hyperplane equivalent to x in A.

### Informal sketch
* The theorem `HYPERPLANE_EQUIV_REFL` asserts the reflexivity of the `hyperplane_equiv` relation.
* The proof involves a straightforward application of the `REWRITE_TAC` tactic to rewrite the `hyperplane_equiv` relation, leveraging its definition to establish the reflexivity property.
* The key insight is that the `hyperplane_equiv` relation is reflexive by definition, as every element is related to itself.

### Mathematical insight
The `HYPERPLANE_EQUIV_REFL` theorem establishes a fundamental property of the `hyperplane_equiv` relation, namely that it is reflexive. This property is essential in various geometric and algebraic contexts, where equivalence relations are used to identify or classify objects. The theorem provides a basis for further results that rely on the reflexivity of `hyperplane_equiv`.

### Dependencies
* `hyperplane_equiv`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of universal quantification and the `REWRITE_TAC` tactic. In some systems, the equivalent of `REWRITE_TAC` might be a `rewrite` or `subst` tactic, and the quantifier might be expressed using a different syntax. Additionally, the definition of `hyperplane_equiv` should be ported and available in the target system.

---

## HYPERPLANE_EQUIV_SYM

### Name of formal statement
HYPERPLANE_EQUIV_SYM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_SYM = prove
 (`!A x y. hyperplane_equiv A x y <=> hyperplane_equiv A y x`,
  REWRITE_TAC[hyperplane_equiv; EQ_SYM_EQ])
```

### Informal statement
For all sets A and all points x and y, the statement "x is hyperplane equivalent to y in A" is logically equivalent to "y is hyperplane equivalent to x in A".

### Informal sketch
* The proof involves showing that the `hyperplane_equiv` relation is symmetric.
* The `REWRITE_TAC` tactic is used with the `hyperplane_equiv` definition and the `EQ_SYM_EQ` theorem to establish this symmetry.
* The key logical stage is recognizing that `hyperplane_equiv A x y` implies `hyperplane_equiv A y x` by the definition of equivalence relations and the specific properties of hyperplane equivalence.
* The use of `EQ_SYM_EQ` theorem suggests that the equivalence relation's symmetric property is being leveraged to prove the theorem.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the `hyperplane_equiv` relation, which is crucial for geometric and algebraic manipulations involving hyperplanes. The symmetry property ensures that the relation behaves as expected under interchange of points, which is a basic requirement for equivalence relations.

### Dependencies
* `hyperplane_equiv`
* `EQ_SYM_EQ`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to how equivalence relations and symmetry are handled. Some systems may have built-in support for proving symmetry properties of relations, while others may require explicit proof steps. Additionally, the `REWRITE_TAC` tactic and its equivalent in the target system should be used to apply the `hyperplane_equiv` definition and `EQ_SYM_EQ` theorem appropriately.

---

## HYPERPLANE_EQUIV_TRANS

### Name of formal statement
HYPERPLANE_EQUIV_TRANS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_TRANS = prove
 (`!A x y z.
        hyperplane_equiv A x y /\ hyperplane_equiv A y z
        ==> hyperplane_equiv A x z`,
  REWRITE_TAC[hyperplane_equiv] THEN MESON_TAC[]);;
```

### Informal statement
For all sets A and points x, y, z, if x is hyperplane equivalent to y with respect to A, and y is hyperplane equivalent to z with respect to A, then x is hyperplane equivalent to z with respect to A.

### Informal sketch
* The proof starts by assuming `hyperplane_equiv A x y` and `hyperplane_equiv A y z`.
* It then applies the definition of `hyperplane_equiv` to these assumptions using `REWRITE_TAC[hyperplane_equiv]`.
* The `MESON_TAC[]` tactic is used to automatically derive the conclusion `hyperplane_equiv A x z` from the rewritten assumptions.
* The key logical stage involves using the transitivity of the equivalence relation implied by `hyperplane_equiv` to chain the equivalences between x, y, and z.

### Mathematical insight
This theorem establishes the transitive property of the `hyperplane_equiv` relation, which is crucial for demonstrating that this relation is indeed an equivalence relation. The transitivity is essential in geometric and algebraic contexts where `hyperplane_equiv` is used to classify or identify points based on their relationship with a hyperplane.

### Dependencies
* `hyperplane_equiv`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how each system handles equivalence relations and transitivity proofs. Some systems may have built-in support for proving equivalence relations or may require explicit proof of reflexivity, symmetry, and transitivity. Additionally, the automation level and tactic structure may differ, so it's essential to understand the underlying mathematical structure to recreate the proof effectively.

---

## HYPERPLANE_EQUIV_UNION

### Name of formal statement
HYPERPLANE_EQUIV_UNION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_UNION = prove
 (`!A B x y. hyperplane_equiv (A UNION B) x y <=>
                hyperplane_equiv A x y /\ hyperplane_equiv B x y`,
  REWRITE_TAC[hyperplane_equiv; IN_UNION] THEN MESON_TAC[]);;
```

### Informal statement
For all sets A and B, and for all points x and y, the points x and y are equivalent with respect to the hyperplane of the union of A and B if and only if x and y are equivalent with respect to the hyperplane of A and x and y are equivalent with respect to the hyperplane of B.

### Informal sketch
* The proof involves rewriting the `hyperplane_equiv` relation using the definition of `IN_UNION` to break down the union of sets A and B.
* The `REWRITE_TAC` tactic is used to apply the definitions of `hyperplane_equiv` and `IN_UNION`.
* The `MESON_TAC` tactic is then used to simplify and derive the conclusion, likely involving basic logical deductions.

### Mathematical insight
This theorem provides a key property of hyperplane equivalence in relation to set union, allowing for the decomposition of equivalence checks over unions into checks over individual sets. This is important for simplifying and composing geometric or topological arguments involving hyperplanes and set operations.

### Dependencies
* `hyperplane_equiv`
* `IN_UNION`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to how each system handles set union and equivalence relations. The use of `REWRITE_TAC` and `MESON_TAC` in HOL Light may correspond to similar rewriting and simplification tactics in other systems, such as `rewrite` in Coq or `simp` in Isabelle. Ensure that the ported version correctly captures the logical structure and quantifiers present in the original HOL Light statement.

---

## hyperplane_cell

### Name of formal statement
hyperplane_cell

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let hyperplane_cell = new_definition `hyperplane_cell A c <=> ?x. c = hyperplane_equiv A x`
```

### Informal statement
The `hyperplane_cell` is defined such that for a given set `A` and a cell `c`, `hyperplane_cell A c` holds if and only if there exists an `x` such that `c` is equal to the hyperplane equivalence class of `A` at `x`.

### Informal sketch
* The definition of `hyperplane_cell` involves an existential quantifier, indicating that to prove `hyperplane_cell A c`, one must exhibit an `x` satisfying the condition `c = hyperplane_equiv A x`.
* The `hyperplane_equiv A x` term suggests the use of equivalence classes defined by a hyperplane arrangement, implying that `c` must be a cell within this arrangement.
* To construct a proof, one would need to identify a suitable `x` for a given `A` and `c`, and then show that `c` matches the `hyperplane_equiv A x`, leveraging properties of hyperplane arrangements and equivalence relations.

### Mathematical insight
The `hyperplane_cell` definition is crucial for formalizing and reasoning about hyperplane arrangements, which are fundamental in geometric and topological studies. It captures the notion of a cell within such an arrangement, allowing for precise statements and proofs about the geometric and combinatorial properties of these structures.

### Dependencies
#### Definitions
* `hyperplane_equiv`
#### Theorems
None explicitly mentioned, but likely dependencies include properties of equivalence relations and hyperplane arrangements.

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how existential quantification and equivalence relations are handled. Specifically, ensure that the representation of `hyperplane_equiv` and the quantifier `?x` are correctly translated, as these are crucial for the definition's meaning. Additionally, consider the library support for geometric and topological concepts in the target system, as this may influence how `hyperplane_cell` and related definitions are best expressed.

---

## HYPERPLANE_CELL

### Name of formal statement
HYPERPLANE_CELL

### Type of the formal statement
new_definition or theorem (likely a definition given the structure, but could be a theorem depending on context)

### Formal Content
```ocaml
let HYPERPLANE_CELL = prove
 (`hyperplane_cell A c <=> ?x. c = {y | hyperplane_equiv A x y}`,
  REWRITE_TAC[EXTENSION; hyperplane_cell; IN_ELIM_THM; IN] THEN
  MESON_TAC[])
```

### Informal statement
The `HYPERPLANE_CELL` statement defines a condition where a set `c` is considered a hyperplane cell of set `A` if and only if there exists an element `x` such that `c` is equal to the set of all elements `y` that are hyperplane equivalent to `x` in `A`.

### Informal sketch
* The definition or theorem involves proving an equivalence between being a `hyperplane_cell` and a specific set condition involving `hyperplane_equiv`.
* The proof strategy involves rewriting the statement using `EXTENSION`, `hyperplane_cell`, `IN_ELIM_THM`, and `IN` to transform the expression into a form where `MESON_TAC` can be applied to derive the conclusion.
* Key steps likely involve manipulating set equalities and memberships, leveraging the properties of `hyperplane_equiv` to establish the necessary and sufficient conditions for a set to be considered a `hyperplane_cell`.

### Mathematical insight
This statement is crucial for defining or characterizing hyperplane cells within a set `A`, based on the equivalence relation `hyperplane_equiv`. It provides a foundational element for further geometric or algebraic analyses, especially in contexts where hyperplane equivalence plays a significant role, such as in geometric or combinatorial structures.

### Dependencies
- **Theorems and Definitions:**
  - `EXTENSION`
  - `hyperplane_cell`
  - `IN_ELIM_THM`
  - `IN`
  - `hyperplane_equiv`
- **Inductive Rules:** None explicitly mentioned, but may depend on the definition of `hyperplane_equiv` and other underlying structures.

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how set equality and membership are handled, as well as how tactical proofs are structured in the target system. The use of `REWRITE_TAC` and `MESON_TAC` suggests that the proof involves straightforward but potentially complex manipulations of set theory and equivalence relations, which might be automated differently in other systems. Additionally, ensure that the `hyperplane_equiv` relation and its properties are appropriately defined and accessible in the target system.

---

## NOT_HYPERPLANE_CELL_EMPTY

### Name of formal statement
NOT_HYPERPLANE_CELL_EMPTY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NOT_HYPERPLANE_CELL_EMPTY = prove
 (`!A. ~(hyperplane_cell A {})`,
  REWRITE_TAC[hyperplane_cell; EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[HYPERPLANE_EQUIV_REFL; IN]);;
```

### Informal statement
For all sets A, it is not the case that the hyperplane cell of A with respect to the empty set is true.

### Informal sketch
* The proof starts with a universal quantification over sets A, considering the `hyperplane_cell` of A with respect to the empty set.
* The `REWRITE_TAC` tactic is applied to rewrite the `hyperplane_cell` using its definition, as well as the `EXTENSION` and `NOT_IN_EMPTY` theorems.
* The `MESON_TAC` tactic is then applied with the `HYPERPLANE_EQUIV_REFL` and `IN` theorems to derive the conclusion that the `hyperplane_cell` of A with respect to the empty set is false.

### Mathematical insight
This theorem provides insight into the properties of hyperplane cells, specifically that the hyperplane cell of any set with respect to the empty set is empty. This is likely an important foundation for further results in the theory of hyperplane cells.

### Dependencies
* Theorems:
  + `HYPERPLANE_EQUIV_REFL`
  + `EXTENSION`
  + `NOT_IN_EMPTY`
  + `IN`
* Definitions:
  + `hyperplane_cell`

### Porting notes
When translating this theorem into another proof assistant, note that the `REWRITE_TAC` and `MESON_TAC` tactics may not have direct counterparts. Instead, the rewrites and derivations may need to be performed using the target system's own mechanisms for rewriting and proof search. Additionally, the `HYPERPLANE_EQUIV_REFL` and `IN` theorems may need to be ported or re-proven in the target system before this theorem can be translated.

---

## NONEMPTY_HYPERPLANE_CELL

### Name of formal statement
NONEMPTY_HYPERPLANE_CELL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NONEMPTY_HYPERPLANE_CELL = prove
 (`!A c. hyperplane_cell A c ==> ~(c = {})`,
  MESON_TAC[NOT_HYPERPLANE_CELL_EMPTY]);;
```

### Informal statement
For all sets A and c, if c is a hyperplane cell of A, then c is not equal to the empty set.

### Informal sketch
* The proof assumes `hyperplane_cell A c` and aims to show `~(c = {})`.
* It utilizes the `NOT_HYPERPLANE_CELL_EMPTY` theorem, suggesting that the non-emptiness of a hyperplane cell is a known property.
* The `MESON_TAC` tactic implies a straightforward, logical deduction from the given assumptions and known theorems.
* The overall strategy is to apply known properties of hyperplane cells to derive the non-emptiness of c.

### Mathematical insight
This theorem is important because it establishes a fundamental property of hyperplane cells, namely that they are non-empty. This property is likely crucial in various geometric and topological contexts where hyperplane cells are used, ensuring that these cells have a non-trivial structure.

### Dependencies
#### Theorems
* `NOT_HYPERPLANE_CELL_EMPTY`

### Porting notes
When translating this theorem into other proof assistants, ensure that the equivalent of `NOT_HYPERPLANE_CELL_EMPTY` is established or imported. The `MESON_TAC` tactic, which performs a simple logical deduction, might be replaced with a similar tactic or a direct proof in the target system, leveraging its automation or logical reasoning capabilities.

---

## UNIONS_HYPERPLANE_CELLS

### Name of formal statement
UNIONS_HYPERPLANE_CELLS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let UNIONS_HYPERPLANE_CELLS = prove
 (`!A. UNIONS {c | hyperplane_cell A c} = (:real^N)`,
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNIV; IN_ELIM_THM] THEN
  REWRITE_TAC[hyperplane_cell] THEN MESON_TAC[HYPERPLANE_EQUIV_REFL; IN]);;
```

### Informal statement
For all sets A, the union of all cells c such that c is a hyperplane cell of A is equal to the set of all real numbers raised to the power of N.

### Informal sketch
* The proof starts by considering the definition of `UNIONS` and its relation to the set of all real numbers raised to the power of N.
* It then applies the `EXTENSION` tactic to rewrite the statement in terms of set membership.
* The `IN_UNIONS`, `IN_UNIV`, and `IN_ELIM_THM` theorems are used to further simplify the statement.
* The `hyperplane_cell` definition is then applied to rewrite the condition for a cell to be a hyperplane cell of A.
* Finally, the `MESON_TAC` tactic is used with the `HYPERPLANE_EQUIV_REFL` and `IN` theorems to derive the conclusion.

### Mathematical insight
This theorem provides a characterization of the union of hyperplane cells in terms of the set of all real numbers raised to the power of N. It is likely used in the development of geometric or topological properties of hyperplane cells, and relies on the `hyperplane_cell` definition and related theorems.

### Dependencies
* Theorems:
	+ `EXTENSION`
	+ `IN_UNIONS`
	+ `IN_UNIV`
	+ `IN_ELIM_THM`
	+ `HYPERPLANE_EQUIV_REFL`
	+ `IN`
* Definitions:
	+ `hyperplane_cell`
	+ `UNIONS`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `UNIONS` and `hyperplane_cell` definitions are translated correctly. Additionally, the `MESON_TAC` tactic may need to be replaced with a similar tactic or a manual proof step, depending on the capabilities of the target system.

---

## DISJOINT_HYPERPLANE_CELLS

### Name of formal statement
DISJOINT_HYPERPLANE_CELLS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DISJOINT_HYPERPLANE_CELLS = prove
 (`!A c1 c2. hyperplane_cell A c1 /\ hyperplane_cell A c2 /\ ~(c1 = c2)
             ==> DISJOINT c1 c2`,
  REWRITE_TAC[hyperplane_cell] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  ASM_REWRITE_TAC[IN_DISJOINT; IN; EXTENSION] THEN
  ASM_MESON_TAC[HYPERPLANE_EQUIV_TRANS; HYPERPLANE_EQUIV_SYM])
```

### Informal statement
For all sets A and hyperplane cells c1 and c2, if c1 and c2 are hyperplane cells of A and c1 is not equal to c2, then c1 and c2 are disjoint.

### Informal sketch
* The proof starts by assuming `hyperplane_cell A c1`, `hyperplane_cell A c2`, and `~(c1 = c2)`.
* It then uses `REWRITE_TAC` to expand the `hyperplane_cell` definition.
* The `REPEAT STRIP_TAC` is applied to strip the quantifiers and implications.
* The `FIRST_X_ASSUM` with `MP_TAC` and `check (is_neg o concl)` is used to handle the negation in the conclusion.
* The `ASM_REWRITE_TAC` is applied with `IN_DISJOINT`, `IN`, and `EXTENSION` to rewrite the disjointness condition.
* Finally, `ASM_MESON_TAC` is used with `HYPERPLANE_EQUIV_TRANS` and `HYPERPLANE_EQUIV_SYM` to derive the conclusion.

### Mathematical insight
This theorem establishes that distinct hyperplane cells of the same set are disjoint. The proof relies on the properties of hyperplane cells and the definition of disjointness. The `HYPERPLANE_EQUIV_TRANS` and `HYPERPLANE_EQUIV_SYM` theorems are used to establish the equivalence relations between hyperplane cells, which is crucial for proving the disjointness.

### Dependencies
* `hyperplane_cell`
* `DISJOINT`
* `IN_DISJOINT`
* `IN`
* `EXTENSION`
* `HYPERPLANE_EQUIV_TRANS`
* `HYPERPLANE_EQUIV_SYM`

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of `hyperplane_cell` and `DISJOINT` definitions, as well as the `HYPERPLANE_EQUIV_TRANS` and `HYPERPLANE_EQUIV_SYM` theorems. The `REWRITE_TAC` and `ASM_REWRITE_TAC` tactics may need to be replaced with equivalent tactics in the target system, and the `FIRST_X_ASSUM` and `ASM_MESON_TAC` tactics may require careful handling of the conclusion and assumptions.

---

## DISJOINT_HYPERPLANE_CELLS_EQ

### Name of formal statement
DISJOINT_HYPERPLANE_CELLS_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DISJOINT_HYPERPLANE_CELLS_EQ = prove
 (`!A c1 c2. hyperplane_cell A c1 /\ hyperplane_cell A c2
             ==> (DISJOINT c1 c2 <=> ~(c1 = c2))`,
  MESON_TAC[NONEMPTY_HYPERPLANE_CELL; DISJOINT_HYPERPLANE_CELLS;
            SET_RULE `DISJOINT s s <=> s = {}`])
```

### Informal statement
For all sets A and hyperplane cells c1 and c2, if c1 and c2 are hyperplane cells of A, then c1 and c2 are disjoint if and only if c1 is not equal to c2.

### Informal sketch
* The theorem `DISJOINT_HYPERPLANE_CELLS_EQ` is proven using `MESON_TAC`, which applies a set of meson rules to derive the conclusion.
* The proof starts with the assumptions that `c1` and `c2` are `hyperplane_cell`s of `A`.
* It then uses the `NONEMPTY_HYPERPLANE_CELL` and `DISJOINT_HYPERPLANE_CELLS` theorems to establish the relationship between `c1`, `c2`, and the `DISJOINT` property.
* The `SET_RULE` `DISJOINT s s <=> s = {}` is also applied to handle the case where `c1` and `c2` are the same set.

### Mathematical insight
This theorem provides a necessary and sufficient condition for two hyperplane cells to be disjoint, which is a fundamental concept in geometry and topology. The theorem states that two hyperplane cells are disjoint if and only if they are not the same cell, which is an intuitive result.

### Dependencies
* Theorems:
  + `NONEMPTY_HYPERPLANE_CELL`
  + `DISJOINT_HYPERPLANE_CELLS`
  + `SET_RULE `DISJOINT s s <=> s = {}``
* Definitions:
  + `hyperplane_cell`
  + `DISJOINT`

### Porting notes
When porting this theorem to other proof assistants, note that the `MESON_TAC` tactic may not have a direct equivalent. Instead, the proof may need to be reconstructed using the specific tactics and rules available in the target system. Additionally, the `SET_RULE` may need to be replaced with a similar rule or axiom in the target system.

---

## HYPERPLANE_CELL_EMPTY

### Name of formal statement
HYPERPLANE_CELL_EMPTY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_EMPTY = prove
 (`hyperplane_cell {} c <=> c = (:real^N)`,
  REWRITE_TAC[HYPERPLANE_CELL; NOT_IN_EMPTY; hyperplane_equiv] THEN
  SET_TAC[])
```

### Informal statement
The theorem `HYPERPLANE_CELL_EMPTY` states that a hyperplane cell of the empty set is equivalent to the entire real N-dimensional space if and only if the set `c` is equal to the set of all real N-dimensional vectors.

### Informal sketch
* The proof starts by considering the definition of `hyperplane_cell` and its relation to the empty set.
* It then applies the `REWRITE_TAC` tactic to rewrite the `hyperplane_cell` term using the definitions of `HYPERPLANE_CELL`, `NOT_IN_EMPTY`, and `hyperplane_equiv`.
* The `SET_TAC` tactic is used to finalize the proof by handling set-theoretic aspects.
* Key to the proof is understanding how `hyperplane_cell` interacts with the empty set and how this relates to the full `real^N` space.

### Mathematical insight
This theorem provides insight into the geometric and topological properties of hyperplane cells, particularly in relation to the empty set and the full space. It serves as a foundational result for further explorations into the properties of hyperplanes and their intersections in N-dimensional real space.

### Dependencies
* Theorems:
  + `HYPERPLANE_CELL`
  + `NOT_IN_EMPTY`
  + `hyperplane_equiv`
* Definitions:
  + `hyperplane_cell`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles set theory and geometric definitions. The `REWRITE_TAC` and `SET_TAC` tactics may have direct analogs or require manual handling depending on the target system's automation and tactic language. Ensure that the definitions of `HYPERPLANE_CELL`, `NOT_IN_EMPTY`, and `hyperplane_equiv` are correctly ported and understood in the context of the target proof assistant.

---

## HYPERPLANE_CELL_SING_CASES

### Name of formal statement
HYPERPLANE_CELL_SING_CASES

### Type of the formal statement
Theorem

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
           REAL_ARITH `x - y < &0 <=> x < y`))
```

### Informal statement
For all real-valued functions `a` and `b` of `N` variables and for all sets `c` of real numbers, if `c` is a hyperplane cell defined by `{(a, b)}`, then `c` is equal to the set of all `x` such that `a` dot `x` equals `b`, or `c` is equal to the set of all `x` such that `a` dot `x` is less than `b`, or `c` is equal to the set of all `x` such that `a` dot `x` is greater than `b`.

### Informal sketch
* The proof starts by assuming `hyperplane_cell {(a,b)} c`, which means `c` is defined as a hyperplane cell based on the pair `(a, b)`.
* It then applies `REWRITE_TAC` with `HYPERPLANE_CELL` and `hyperplane_equiv` to transform the expression for `c`.
* The `FORALL_UNWIND_THM2`, `IN_SING`, and `hyperplane_side` are used to further simplify the expression, leading to the introduction of a variable `y`.
* The proof proceeds by case analysis on the sign of `(a:real^N) dot y - b` using `REAL_SGN_CASES`, and then applies `ASM_REWRITE_TAC` with `REAL_SGN_EQ` to simplify based on the sign.
* Finally, it uses `SIMP_TAC` with various real arithmetic properties to reach the conclusion about `c`.

### Mathematical insight
This theorem provides a characterization of hyperplane cells in terms of linear inequalities. It's essential in geometric and algebraic reasoning, especially when dealing with half-spaces defined by hyperplanes. The theorem helps in understanding how hyperplane cells can be represented as sets defined by linear equalities or inequalities, which is crucial in various mathematical and computational contexts.

### Dependencies
* `HYPERPLANE_CELL`
* `hyperplane_equiv`
* `FORALL_UNWIND_THM2`
* `IN_SING`
* `hyperplane_side`
* `REAL_SGN_CASES`
* `REAL_SGN_EQ`
* `REAL_SUB_0`
* `REAL_SUB_LT`
* `real_gt`
* `REAL_ARITH`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to how these systems handle real arithmetic, linear algebra, and case analysis. The `REAL_SGN_CASES` and manipulation of real-valued functions might require careful handling due to differences in how these systems represent and manipulate real numbers and their properties. Additionally, the automation level and tactic structure might vary, requiring adjustments to achieve similar proof steps.

---

## HYPERPLANE_CELL_SING

### Name of formal statement
HYPERPLANE_CELL_SING

### Type of the formal statement
Theorem

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
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0] THEN REAL_ARITH_TAC])
```

### Informal statement
For all vectors `a` and real numbers `b`, and for any set `c`, the following holds: `c` is a hyperplane cell defined by `{(a, b)}` if and only if either `a` is the zero vector and `c` is the entire space `ℝ^N`, or `c` is one of the following sets: the set of all `x` such that `a` dot `x` equals `b`, the set of all `x` such that `a` dot `x` is less than `b`, or the set of all `x` such that `a` dot `x` is greater than `b`.

### Informal sketch
* The proof starts by considering the case when `a` is the zero vector. In this case, it shows that `c` must be the entire space `ℝ^N`.
* For non-zero `a`, the proof breaks down into cases based on the definition of `hyperplane_cell`. It uses `COND_CASES_TAC` to split into these cases.
* The proof then applies various rewrite rules and simplifications, including `REWRITE_TAC[hyperplane_cell; hyperplane_equiv; EXTENSION; IN_UNIV]`, to transform the goal into a more manageable form.
* Key steps involve using `REAL_ARITH` to manipulate inequalities and `MATCH_MP_TAC` to apply a specific theorem.
* The proof also involves existential introductions using `EXISTS_TAC` to demonstrate the existence of certain vectors that satisfy specific conditions.
* The use of `ASM_SIMP_TAC` and `REAL_ARITH_TAC` helps to simplify and solve the resulting arithmetic and dot product equations.

### Mathematical insight
This theorem provides a characterization of hyperplane cells in terms of linear inequalities. It shows that a set `c` is a hyperplane cell if it can be defined by a linear equation or inequality of the form `a dot x = b`, `a dot x < b`, or `a dot x > b`, where `a` is a non-zero vector and `b` is a real number. This is a fundamental concept in geometry and is crucial for understanding and working with hyperplanes and their properties.

### Dependencies
#### Theorems
* `hyperplane_cell`
* `hyperplane_equiv`
* `EXTENSION`
* `IN_UNIV`
* `IN_SING`
* `FORALL_UNWIND_THM2`
* `hyperplane_side`
* `DOT_LZERO`
* `REAL_ARITH`
* `REAL_SGN_EQ`
* `REAL_SUB_0`
* `DOT_RMUL`
* `REAL_DIV_RMUL`
* `DOT_EQ_0`
#### Definitions
* `hyperplane_cell`
* `hyperplane_equiv`
* `hyperplane_side`

---

## HYPERPLANE_CELL_UNION

### Name of formal statement
HYPERPLANE_CELL_UNION

### Type of the formal statement
Theorem

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
  MESON_TAC[HYPERPLANE_EQUIV_TRANS; HYPERPLANE_EQUIV_SYM])
```

### Informal statement
For all sets `A` and `B` of real numbers and for all sets `c` of real numbers, the following holds: `c` is a hyperplane cell of `A UNION B` if and only if `c` is not empty and there exist sets `c1` and `c2` such that `c1` is a hyperplane cell of `A`, `c2` is a hyperplane cell of `B`, and `c` is the intersection of `c1` and `c2`.

### Informal sketch
* The proof starts by considering the case when `c` is empty and applying `NONEMPTY_HYPERPLANE_CELL` to handle this case.
* It then proceeds to use `HYPERPLANE_CELL` and `HYPERPLANE_EQUIV_UNION` to relate the hyperplane cell of the union of `A` and `B` to the hyperplane cells of `A` and `B`.
* The proof involves rewriting the set operations using `SET_RULE` and applying `MESON` to simplify the existential quantification.
* The `EQ_TAC` tactic is used to split the equivalence into two implications, and `LEFT_IMP_EXISTS_THM` is applied to handle the existential quantification.
* The proof then involves using `MAP_EVERY X_GEN_TAC` to introduce variables `a` and `b`, and `DISCH_THEN SUBST_ALL_TAC` to substitute and simplify the statement.
* The `MATCH_MP_TAC MONO_EXISTS` tactic is used to apply the `MONO_EXISTS` theorem, and `X_GEN_TAC` is used to introduce a variable `x`.
* The final steps involve rewriting using `EXTENSION`, `IN_INTER`, and `IN_ELIM_THM`, and applying `MESON_TAC` with `HYPERPLANE_EQUIV_TRANS` and `HYPERPLANE_EQUIV_SYM` to conclude the proof.

### Mathematical insight
This theorem provides a way to decompose a hyperplane cell of the union of two sets into the intersection of hyperplane cells of the individual sets. This is useful in geometric and topological contexts where unions and intersections of sets are common operations.

### Dependencies
* Theorems:
  + `NONEMPTY_HYPERPLANE_CELL`
  + `HYPERPLANE_EQUIV_UNION`
  + `MONO_EXISTS`
  + `HYPERPLANE_EQUIV_TRANS`
  + `HYPERPLANE_EQUIV_SYM`
* Definitions:
  + `hyperplane_cell`
  + `UNION`
  + `INTER`

---

## FINITE_HYPERPLANE_CELLS

### Name of formal statement
FINITE_HYPERPLANE_CELLS

### Type of the formal statement
Theorem

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
    REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN MESON_TAC[INTER_COMM]])
```

### Informal statement
For all sets A, if A is finite, then the set of all hyperplane cells c (where c is a function from real^N to bool) such that the hyperplane cell A c holds, is also finite.

### Informal sketch
* The proof starts by applying `FINITE_INDUCT_STRONG` to reduce the problem to the case where A is empty or a singleton.
* The `HYPERPLANE_CELL_EMPTY` and `FINITE_SING` theorems are used to handle the base cases.
* The `FORALL_PAIR_THM` is applied to introduce variables `a` and `b`.
* The `MATCH_MP_TAC FINITE_SUBSET` tactic is used to show that the set of hyperplane cells is finite by exhibiting a finite subset.
* Two main cases are considered:
  + The first case uses `FINITE_PRODUCT_DEPENDENT` to show that the set of hyperplane cells for a singleton set {(a, b)} is finite.
  + The second case uses `HYPERPLANE_CELL_UNION` and `INTER_COMM` to show that the intersection of two hyperplane cells is also a hyperplane cell.

### Mathematical insight
This theorem is important because it shows that the set of hyperplane cells for a finite set A is also finite. This has implications for the study of geometric and topological properties of sets in real space. The proof relies on a combination of inductive reasoning and clever use of existing theorems to establish the finiteness of the set of hyperplane cells.

### Dependencies
#### Theorems
* `FINITE_INDUCT_STRONG`
* `HYPERPLANE_CELL_EMPTY`
* `FINITE_SING`
* `FORALL_PAIR_THM`
* `FINITE_SUBSET`
* `FINITE_PRODUCT_DEPENDENT`
* `HYPERPLANE_CELL_UNION`
* `INTER_COMM`
#### Definitions
* `hyperplane_cell` 

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of the `hyperplane_cell` function and the `FINITE_INDUCT_STRONG` tactic, as these may be implemented differently in other systems. Additionally, the use of `MATCH_MP_TAC` and `ASM_REWRITE_TAC` may need to be adapted to the target system's tactic language.

---

## FINITE_RESTRICT_HYPERPLANE_CELLS

### Name of formal statement
FINITE_RESTRICT_HYPERPLANE_CELLS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FINITE_RESTRICT_HYPERPLANE_CELLS = prove
 (`!P A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c /\ P c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c:real^N->bool | hyperplane_cell A c}` THEN
  ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLS] THEN SET_TAC[])
```

### Informal statement
For all predicates `P` and all sets `A`, if `A` is finite, then the set of all functions `c` from `real^N` to `bool` such that `c` is a hyperplane cell of `A` and `P c` holds, is finite.

### Informal sketch
* The proof starts by assuming `A` is finite and `P` is a predicate.
* It uses `REPEAT STRIP_TAC` to strip the universal quantifier and implication, setting up the goal to prove finiteness.
* The `MATCH_MP_TAC FINITE_SUBSET` tactic is applied to reduce the problem to showing that the set of hyperplane cells of `A` is finite, leveraging the `FINITE_SUBSET` theorem.
* The `EXISTS_TAC` tactic is used to introduce the set of hyperplane cells of `A`, which is then shown to be finite using `ASM_SIMP_TAC` with `FINITE_HYPERPLANE_CELLS`.
* Finally, `SET_TAC` is applied to conclude the proof.

### Mathematical insight
This theorem provides a condition under which the set of hyperplane cells of a finite set `A`, restricted by a predicate `P`, is also finite. This is important in geometric and topological contexts where the finiteness of such sets can have significant implications for the structure and properties of spaces.

### Dependencies
#### Theorems
* `FINITE_SUBSET`
* `FINITE_HYPERPLANE_CELLS`

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to handling the predicate `P`, the set `A`, and the concept of hyperplane cells, as different systems may represent these differently. Additionally, the use of `REPEAT STRIP_TAC` and `MATCH_MP_TAC` may need to be adapted, as these tactics might not have direct counterparts in other systems.

---

## FINITE_SET_OF_HYPERPLANE_CELLS

### Name of formal statement
FINITE_SET_OF_HYPERPLANE_CELLS

### Type of the formal statement
Theorem

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
For all sets A and C, if A is finite and for every function c from real^N to bool that is in C, c is a hyperplane cell of A, then C is finite.

### Informal sketch
* The proof starts by assuming `FINITE A` and a set `C` such that every `c` in `C` satisfies `hyperplane_cell A c`.
* It then applies the `FINITE_SUBSET` theorem to show that if `C` is a subset of a finite set, then `C` is finite.
* The proof constructs a set `{c:real^N->bool | hyperplane_cell A c}` and shows it is finite using `FINITE_HYPERPLANE_CELLS`.
* By demonstrating `C` is a subset of this finite set, it concludes `C` is finite.
* Key steps involve using `REPEAT STRIP_TAC` to strip away the quantifiers and implications, and `MATCH_MP_TAC` to apply the `FINITE_SUBSET` theorem.

### Mathematical insight
This theorem is important because it establishes a relationship between the finiteness of a set `A` and the finiteness of a set `C` of hyperplane cells defined over `A`. It provides a way to reason about the finiteness of collections of geometric objects (hyperplane cells) in terms of the finiteness of their defining sets, which is crucial in various geometric and topological arguments.

### Dependencies
* Theorems:
  - `FINITE_SUBSET`
  - `FINITE_HYPERPLANE_CELLS`
* Definitions:
  - `FINITE`
  - `hyperplane_cell`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how each system handles quantifiers, set comprehensions, and the application of theorems like `FINITE_SUBSET`. The use of `REPEAT STRIP_TAC` and `MATCH_MP_TAC` may need to be adapted, as different systems have different tactics for similar purposes. Additionally, ensure that the target system's library includes or can easily define equivalents of `FINITE_HYPERPLANE_CELLS` and `FINITE_SUBSET`.

---

## PAIRWISE_DISJOINT_HYPERPLANE_CELLS

### Name of formal statement
PAIRWISE_DISJOINT_HYPERPLANE_CELLS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PAIRWISE_DISJOINT_HYPERPLANE_CELLS = prove
 (`!A C. (!c. c IN C ==> hyperplane_cell A c)
         ==> pairwise DISJOINT C`,
  REWRITE_TAC[pairwise] THEN MESON_TAC[DISJOINT_HYPERPLANE_CELLS])
```

### Informal statement
For all sets A and collections C, if for every c in C, c is a hyperplane cell of A, then the elements of C are pairwise disjoint.

### Informal sketch
* The proof starts by assuming that for every c in C, c is a `hyperplane_cell` of A.
* It then applies the `REWRITE_TAC` tactic with the `pairwise` definition to express the pairwise disjointness of C in terms of the `DISJOINT` relation.
* The `MESON_TAC` tactic is used with the `DISJOINT_HYPERPLANE_CELLS` theorem to derive the conclusion that C is pairwise disjoint.
* The key logical stage involves recognizing that the `hyperplane_cell` property implies disjointness, which is then lifted to the collection level using `pairwise`.

### Mathematical insight
This theorem provides a way to establish that a collection of hyperplane cells is pairwise disjoint, which is essential in various geometric and topological arguments. The intuition behind this statement is that hyperplane cells, by definition, have a specific geometric structure that prevents them from overlapping, except possibly at their boundaries.

### Dependencies
* Theorems:
  * `DISJOINT_HYPERPLANE_CELLS`
* Definitions:
  * `pairwise`
  * `hyperplane_cell`
  * `DISJOINT`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of `pairwise` and `DISJOINT` properties, as different systems may have varying levels of automation for such relational properties. Additionally, the `MESON_TAC` tactic, which is used for automated reasoning, might need to be replaced with a similar tactic or a manual proof step, depending on the target system's capabilities.

---

## HYPERPLANE_CELL_INTER_OPEN_AFFINE

### Name of formal statement
HYPERPLANE_CELL_INTER_OPEN_AFFINE

### Type of the formal statement
Theorem

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
For all sets $A$ of real numbers and all $c$, if $A$ is finite and $c$ is a hyperplane cell of $A$, then there exist sets $s$ and $t$ such that $s$ is open, $t$ is affine, and $c$ is equal to the intersection of $s$ and $t$.

### Informal sketch
* The proof proceeds by induction on the finiteness of $A$, using `FINITE_INDUCT_STRONG`.
* The base case is when $A$ is empty, in which case `HYPERPLANE_CELL_EMPTY` is used to show that $c$ is the entire space, and thus can be represented as the intersection of the open set $s = \mathbb{R}^N$ and the affine set $t = \mathbb{R}^N$.
* For the inductive step, the `FORALL_PAIR_THM` is used to introduce variables `a`, `b`, and `A'`, and `HYPERPLANE_CELL_UNION` is used to express $c$ as a union of hyperplane cells.
* The proof then considers cases based on the definition of hyperplane cells and uses various properties of open and affine sets, such as `OPEN_UNIV`, `AFFINE_UNIV`, `INTER_UNIV`, `AFFINE_INTER`, `OPEN_INTER`, `AFFINE_HYPERPLANE`, `OPEN_HALFSPACE_LT`, and `OPEN_HALFSPACE_GT`, to construct the required sets $s$ and $t$.
* The `COND_CASES_TAC` and `REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC)` tactics are used to handle different cases and substitute assumptions.

### Mathematical insight
This theorem provides a way to decompose a hyperplane cell into the intersection of an open set and an affine set. This decomposition is useful in various geometric and topological arguments, as it allows for the application of properties and theorems that are specific to open and affine sets. The theorem relies on the finiteness of the set $A$, which ensures that the hyperplane cell can be expressed as a finite union of simpler sets.

### Dependencies
* Theorems:
	+ `FINITE_INDUCT_STRONG`
	+ `HYPERPLANE_CELL_EMPTY`
	+ `FORALL_PAIR_THM`
	+ `HYPERPLANE_CELL_UNION`
	+ `AFFINE_INTER`
	+ `OPEN_INTER`
	+ `AFFINE_HYPERPLANE`
	+ `OPEN_HALFSPACE_LT`
	+ `OPEN_HALFSPACE_GT`
* Definitions:
	+ `hyperplane_cell`
	+ `open`
	+ `affine`
	+ `INTER`
	+ `UNION`

---

## HYPERPLANE_CELL_RELATIVELY_OPEN

### Name of formal statement
HYPERPLANE_CELL_RELATIVELY_OPEN

### Type of the formal statement
Theorem

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
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_SIMP_TAC[OPEN_IN_OPEN_INTER]])
```

### Informal statement
For all sets $A$ and $c$, if $A$ is finite and $c$ is a hyperplane cell of $A$, then $c$ is open in the subtopology of the Euclidean space induced by the affine hull of $c$. Formally, $\forall A \, c: \mathbb{R}^N \to \mathbb{B}, \, \text{FINITE}(A) \land \text{hyperplane\_cell}(A, c) \Rightarrow \text{open\_in}(\text{subtopology}(\text{euclidean}, \text{affine\_hull}(c)), c)$.

### Informal sketch
* The proof starts by assuming the premises: $A$ is finite and $c$ is a hyperplane cell of $A$.
* It uses the `HYPERPLANE_CELL_INTER_OPEN_AFFINE` theorem to derive an implication involving the openness of $c$ in the affine hull.
* The proof then proceeds by case analysis on whether the intersection of two sets $s$ and $t$ is empty, utilizing `OPEN_IN_EMPTY` for the empty case.
* For the non-empty case, it applies `AFFINE_HULL_CONVEX_INTER_OPEN` and `AFFINE_IMP_CONVEX` to establish the openness of $c$ in the subtopology.
* Key steps involve substituting equalities and using `EQ_TRANS` to chain equalities, as well as applying `MATCH_MP_TAC` to use specific theorems like `AFFINE_HULL_EQ`.

### Mathematical insight
This theorem is crucial because it establishes a property of hyperplane cells in relation to their openness in a specific subtopology. Hyperplane cells are significant in geometric and topological studies, especially in understanding the structure of spaces and sets defined by linear inequalities. The theorem provides insight into how these cells behave under certain topological operations, which is essential for more advanced geometric and analytical constructions.

### Dependencies
#### Theorems
* `HYPERPLANE_CELL_INTER_OPEN_AFFINE`
* `AFFINE_HULL_CONVEX_INTER_OPEN`
* `AFFINE_IMP_CONVEX`
* `OPEN_IN_EMPTY`
* `AFFINE_HULL_EQ`
#### Definitions
* `FINITE`
* `hyperplane_cell`
* `open_in`
* `subtopology`
* `euclidean`
* `affine_hull`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles:
- Quantifiers and their scope
- Set operations and predicates
- Topological concepts like openness and subtopologies
- Affine hulls and geometric constructions
- The `MATCH_MP_TAC` and `SUBGOAL_THEN` tactics may need to be reinterpreted in terms of the target system's tactic language, potentially involving more explicit use of lemmas and theorem application.

---

## HYPERPLANE_CELL_RELATIVE_INTERIOR

### Name of formal statement
HYPERPLANE_CELL_RELATIVE_INTERIOR

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_RELATIVE_INTERIOR = prove
(`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> relative_interior c = c`,
  MESON_TAC[RELATIVE_INTERIOR_OPEN_IN; HYPERPLANE_CELL_RELATIVELY_OPEN])
```

### Informal statement
For all sets A of real-valued functions and all sets c, if A is finite and c is a hyperplane cell defined by A, then the relative interior of c is equal to c.

### Informal sketch
* The theorem `HYPERPLANE_CELL_RELATIVE_INTERIOR` is proved by applying `MESON_TAC` to two key lemmas: `RELATIVE_INTERIOR_OPEN_IN` and `HYPERPLANE_CELL_RELATIVELY_OPEN`.
* The proof involves showing that for any finite set A and hyperplane cell c defined by A, the relative interior of c coincides with c itself.
* The `MESON_TAC` tactic is used to combine the given lemmas and derive the conclusion.

### Mathematical insight
This theorem provides insight into the geometric structure of hyperplane cells, showing that their relative interiors are equal to the cells themselves. This result is likely important in geometric and topological arguments, where understanding the relative interior of sets is crucial.

### Dependencies
* Theorems:
  + `RELATIVE_INTERIOR_OPEN_IN`
  + `HYPERPLANE_CELL_RELATIVELY_OPEN`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of `FINITE` sets and the definition of `hyperplane_cell`. Additionally, ensure that the `relative_interior` function is defined and behaves as expected in the target system. The `MESON_TAC` tactic may need to be replaced with equivalent tactics or proof combinators in the target system.

---

## HYPERPLANE_CELL_CONVEX

### Name of formal statement
HYPERPLANE_CELL_CONVEX

### Type of the formal statement
Theorem

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
              CONVEX_HYPERPLANE])
```

### Informal statement
For all sets `A` and functions `c` from `real^N` to `bool`, if `c` is a hyperplane cell of `A`, then `c` is convex.

### Informal sketch
* The proof starts by assuming `hyperplane_cell A c` and aims to show `convex c`.
* It uses `REWRITE_TAC[HYPERPLANE_CELL]` to expand the definition of `hyperplane_cell`.
* The proof then employs `DISCH_THEN` and `X_CHOOSE_THEN` to handle the existential quantifier in `hyperplane_cell`.
* It applies `REWRITE_TAC[hyperplane_equiv]` to utilize the equivalence definition of a hyperplane.
* The `ONCE_REWRITE_TAC` and `REWRITE_TAC` with various rules are used to manipulate the set and logical expressions, ultimately aiming to apply `CONVEX_INTERS`.
* The proof then proceeds with `MAP_EVERY X_GEN_TAC` to introduce variables `a` and `b`, and `DISCH_TAC` to discharge assumptions.
* It uses `CONV_TAC` for conversion, `REWRITE_TAC[hyperplane_side]`, and `REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC` with `REAL_SGN_CASES` to handle cases based on the sign of the dot product.
* Finally, it simplifies using `ASM_REWRITE_TAC` and `SIMP_TAC` with various arithmetic properties to establish the convexity of `c`.

### Mathematical insight
This theorem is important because it establishes a fundamental property of hyperplane cells, which are central in geometry and convex analysis. A hyperplane cell being convex means that for any two points within the cell, the line segment connecting them also lies entirely within the cell. This property has numerous implications in optimization, geometry, and other areas of mathematics.

### Dependencies
#### Theorems
* `CONVEX_INTERS`
* `CONVEX_HALFSPACE_LT`
* `CONVEX_HALFSPACE_GT`
* `CONVEX_HYPERPLANE`
#### Definitions
* `hyperplane_cell`
* `hyperplane_equiv`
* `convex`
* `hyperplane_side`
#### Rules
* `REAL_SGN_CASES`
* `REAL_SUB_0`
* `REAL_ARITH` 

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles binders, quantifiers, and set operations. The use of `REPEAT`, `DISCH_THEN`, and `MAP_EVERY` tactics might need to be adapted, as different systems have different tactical languages. Additionally, the `CONV_TAC` and `SIMP_TAC` may require adjustments due to differences in conversion and simplification mechanisms. Ensure that the target system's libraries include equivalents for `REAL_SGN_CASES`, `REAL_SUB_0`, and `REAL_ARITH` to facilitate a smooth translation.

---

## HYPERPLANE_CELL_INTERS

### Name of formal statement
HYPERPLANE_CELL_INTERS

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[HYPERPLANE_EQUIV_SYM; HYPERPLANE_EQUIV_TRANS])
```

### Informal statement
For all sets $A$ and collections $C$ of functions from $\mathbb{R}^N$ to $\mathbb{R}$, if every function $c$ in $C$ is a hyperplane cell of $A$, and $C$ is non-empty and has a non-empty intersection, then the intersection of all functions in $C$ is also a hyperplane cell of $A$.

### Informal sketch
* Start by assuming $A$ and $C$ satisfy the given conditions.
* Use `GEN_TAC` to introduce a variable $z$ of type `real^N` and apply `REWRITE_TAC` with `HYPERPLANE_CELL` and `GSYM MEMBER_NOT_EMPTY` to set up the hyperplane cell condition.
* Employ `MATCH_MP_TAC MONO_EXISTS` to apply the `MONO_EXISTS` theorem, introducing a new variable `z` of type `real^N`.
* Apply `REWRITE_TAC` with `IN_INTERS` to express the intersection condition and `GEN_REWRITE_TAC` with `EXTENSION` to rewrite the extensionality of the intersection.
* Introduce a new variable `x` of type `real^N` using `X_GEN_TAC` and apply `EQ_TAC` to reason about the equality of the intersection.
* Use `FIRST_X_ASSUM` with `X_CHOOSE_TAC` to choose a function `c` in `C` and `REPEAT` with `FIRST_X_ASSUM` and `MP_TAC` to apply the assumptions to `c`.
* Apply `ASM_REWRITE_TAC` and `REPEAT DISCH_TAC` to simplify the assumptions and `FIRST_X_ASSUM` with `CHOOSE_THEN SUBST_ALL_TAC` to substitute the chosen function.
* Finally, apply `RULE_ASSUM_TAC` with `REWRITE_RULE` and `IN_ELIM_THM`, and `SIMP_TAC` with `IN_ELIM_THM` to simplify the conclusion, and `ASM_MESON_TAC` with `HYPERPLANE_EQUIV_SYM` and `HYPERPLANE_EQUIV_TRANS` to derive the final result.

### Mathematical insight
This theorem provides a way to reason about the intersection of hyperplane cells, which is essential in geometric and topological arguments. The hyperplane cell condition ensures that each function in $C$ separates the space into two regions, and the intersection of these functions represents the common region. The theorem shows that this intersection is also a hyperplane cell, allowing for further reasoning about the geometric properties of the space.

### Dependencies
* Theorems:
  + `MONO_EXISTS`
  + `HYPERPLANE_EQUIV_SYM`
  + `HYPERPLANE_EQUIV_TRANS`
* Definitions:
  + `hyperplane_cell`
  + `INTERS`
  + `IN_INTERS`
  + `IN_ELIM_THM`
  + `EXTENSION`
  + `MEMBER_NOT_EMPTY`

---

## HYPERPLANE_CELL_INTER

### Name of formal statement
HYPERPLANE_CELL_INTER

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_INTER = prove
 (`!A s t:real^N->bool.
        hyperplane_cell A s /\ hyperplane_cell A t /\ ~(s INTER t = {})
        ==> hyperplane_cell A (s INTER t)`,
  REWRITE_TAC[GSYM INTERS_2] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HYPERPLANE_CELL_INTERS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; NOT_INSERT_EMPTY])
```

### Informal statement
For all sets `A` and all real-valued functions `s` and `t` of `N` variables that range over the real numbers to boolean values, if `s` and `t` are both hyperplane cells of `A` and the intersection of `s` and `t` is not empty, then the intersection of `s` and `t` is also a hyperplane cell of `A`.

### Informal sketch
* The proof starts by assuming that `s` and `t` are hyperplane cells of `A` and that their intersection is not empty.
* It then applies a rewrite tactic to transform the expression `s INTER t` using the `GSYM INTERS_2` rule.
* The `REPEAT STRIP_TAC` tactic is applied to remove any universal quantifiers and implications, preparing the statement for further manipulation.
* The `MATCH_MP_TAC HYPERPLANE_CELL_INTERS` tactic is used to match the current goal with a previously proved theorem `HYPERPLANE_CELL_INTERS`, which likely establishes a property of hyperplane cell intersections.
* Finally, `ASM_REWRITE_TAC` is applied with several rules (`FORALL_IN_INSERT`, `NOT_IN_EMPTY`, `NOT_INSERT_EMPTY`) to simplify the expression and reach the desired conclusion.

### Mathematical insight
This theorem provides a key property of hyperplane cells, showing that the intersection of two hyperplane cells of a set `A` (provided the intersection is not empty) is itself a hyperplane cell of `A`. This is important for understanding the geometric and topological structure of sets defined by hyperplane cells, and it has implications for various applications in geometry, analysis, and computer science.

### Dependencies
* Theorems:
  * `HYPERPLANE_CELL_INTERS`
* Definitions:
  * `hyperplane_cell`
  * `INTER`
* Other:
  * `GSYM INTERS_2`
  * `FORALL_IN_INSERT`
  * `NOT_IN_EMPTY`
  * `NOT_INSERT_EMPTY`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to the handling of quantifiers, implications, and the `INTER` operation, as these may be represented differently. The `MATCH_MP_TAC` and `ASM_REWRITE_TAC` tactics may need to be replaced with equivalent tactics in the target system, and the `HYPERPLANE_CELL_INTERS` theorem will need to be ported as well. Additionally, the representation of real-valued functions and boolean values may vary between systems, requiring careful consideration to ensure a correct translation.

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
            s = UNIONS t`
```

### Informal statement
The `hyperplane_cellcomplex` is defined as a relation between a set `A` and a set `s` such that there exists a set `t` of cells, where for all cells `c` in `t`, `c` is a `hyperplane_cell` of `A`, and `s` is the union of all cells in `t`.

### Informal sketch
* The definition involves the existence of a set `t` of cells that satisfy the `hyperplane_cell` property with respect to `A`.
* Each cell `c` in `t` must be a `hyperplane_cell` of `A`.
* The set `s` is defined as the union of all cells in `t`, denoted by `UNIONS t`.
* The definition uses a universal quantifier `!c` to ensure all cells in `t` meet the `hyperplane_cell` criterion.
* The `?t` existential quantifier indicates that there must exist at least one set `t` that satisfies these conditions for `s` to be considered a `hyperplane_cellcomplex` of `A`.

### Mathematical insight
This definition provides a way to describe a complex geometric structure as a collection of simpler components, namely `hyperplane_cell`s, which are combined to form the complex. The `hyperplane_cellcomplex` relation is crucial for constructing and reasoning about geometric objects that can be decomposed into these simpler cells, facilitating proofs and calculations in geometric and topological contexts.

### Dependencies
* `hyperplane_cell`
* `UNIONS`

### Porting notes
When translating this definition into other proof assistants, ensure that the existential and universal quantifiers are properly handled, and that the set union operation `UNIONS` is correctly interpreted. Additionally, the `hyperplane_cell` definition should be ported first, as it is a dependency of this definition. Pay attention to how the target system handles set theory and geometric constructions, as these may differ from HOL Light's approach.

---

## HYPERPLANE_CELLCOMPLEX_EMPTY

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_EMPTY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_EMPTY = prove
 (`!A:real^N#real->bool. hyperplane_cellcomplex A {}`,
  GEN_TAC THEN REWRITE_TAC[hyperplane_cellcomplex] THEN
  EXISTS_TAC `{}:(real^N->bool)->bool` THEN
  REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0])
```

### Informal statement
For all sets $A$ of real-valued functions, the hyperplane cell complex of $A$ with the empty set is true.

### Informal sketch
* The proof starts by generalizing over all sets $A$ of real-valued functions using `GEN_TAC`.
* It then rewrites the `hyperplane_cellcomplex` definition using `REWRITE_TAC`.
* The existence of an empty set of real-valued functions is asserted using `EXISTS_TAC`.
* Finally, the proof is completed by rewriting using `NOT_IN_EMPTY` and `UNIONS_0`, which simplifies the expression to a true statement.

### Mathematical insight
This theorem provides a basic property of hyperplane cell complexes, stating that the complex of any set $A$ with the empty set is always true. This result may serve as a foundation for more complex constructions and theorems involving hyperplane cell complexes.

### Dependencies
* `hyperplane_cellcomplex`
* `NOT_IN_EMPTY`
* `UNIONS_0`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of the `real^N#real->bool` type and the `hyperplane_cellcomplex` definition. Ensure that the target system can represent these constructs and that the proof steps, particularly the use of `REWRITE_TAC` and `EXISTS_TAC`, are appropriately translated.

---

## HYPERPLANE_CELL_CELLCOMPLEX

### Name of formal statement
HYPERPLANE_CELL_CELLCOMPLEX

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_CELLCOMPLEX = prove
 (`!A c:real^N->bool. hyperplane_cell A c ==> hyperplane_cellcomplex A c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hyperplane_cellcomplex] THEN
  EXISTS_TAC `{c:real^N->bool}` THEN
  ASM_SIMP_TAC[IN_SING; UNIONS_1])
```

### Informal statement
For all sets `A` of real-valued functions and all predicates `c` on real-valued functions, if `A` is a hyperplane cell with respect to `c`, then `A` is a hyperplane cell complex with respect to `c`.

### Informal sketch
* The proof begins by assuming `A` is a hyperplane cell with respect to `c`, which implies certain properties about `A` and `c`.
* The `REPEAT STRIP_TAC` suggests stripping away the outermost universal quantifier to work directly with `A` and `c`.
* The proof then rewrites the definition of `hyperplane_cellcomplex` using `REWRITE_TAC[hyperplane_cellcomplex]`, likely to align with the properties of `hyperplane_cell`.
* An existential quantification is introduced via `EXISTS_TAC `{c:real^N->bool}`, indicating the existence of a set (in this case, a singleton set containing `c`) that satisfies certain conditions.
* Finally, `ASM_SIMP_TAC[IN_SING; UNIONS_1]` simplifies the assertion using the properties of singleton sets (`IN_SING`) and unions (`UNIONS_1`), likely to conclude that `A` satisfies the conditions for being a `hyperplane_cellcomplex` with respect to `c`.

### Mathematical insight
This theorem provides a connection between the concepts of hyperplane cells and hyperplane cell complexes, showing that any set `A` that is a hyperplane cell with respect to a predicate `c` also forms a hyperplane cell complex with respect to `c`. This is important for establishing a foundational relationship between these two concepts, potentially simplifying proofs or constructions in geometric or topological contexts.

### Dependencies
* `hyperplane_cell`
* `hyperplane_cellcomplex`
* `IN_SING`
* `UNIONS_1`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how universal and existential quantifiers are handled, as well as how the `REWRITE_TAC` and `EXISTS_TAC` tactics are represented. The treatment of predicates and sets of real-valued functions may also vary between systems, requiring careful consideration to ensure a correct and equivalent formulation.

---

## HYPERPLANE_CELLCOMPLEX_UNIONS

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_UNIONS

### Type of the formal statement
Theorem

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
  ASM SET_TAC[])
```

### Informal statement
For all sets $A$ and all collections $C$ of subsets of $\mathbb{R}^N$, if for every subset $s$ in $C$, $A$ is a hyperplane cell complex of $s$, then $A$ is a hyperplane cell complex of the union of all subsets in $C$.

### Informal sketch
* The proof starts by assuming that $A$ is a hyperplane cell complex for every $s \in C$.
* It then applies the `hyperplane_cellcomplex` definition and uses `RIGHT_IMP_EXISTS_THM` to transform the implication.
* The `SKOLEM_THM` and `LEFT_IMP_EXISTS_THM` are used to handle existential quantification, introducing a function `f` that maps subsets of $\mathbb{R}^N$ to subsets of $\mathbb{R}^N$.
* The proof then constructs the union of the images of $C$ under $f$ and shows that this union satisfies the conditions for being a hyperplane cell complex.
* Key steps involve using `FORALL_IN_UNIONS`, `IMP_CONJ`, and `RIGHT_FORALL_IMP_THM` to reason about the union of subsets and their properties.
* The `GEN_REWRITE_TAC` with `EXTENSION` and further manipulations using `IN_UNIONS` and `IN_ELIM_THM` are used to finalize the proof.

### Mathematical insight
This theorem is important because it allows us to extend the property of being a hyperplane cell complex from individual subsets to their unions, which is crucial in geometric and topological arguments. It provides a way to reason about complex geometric objects by decomposing them into simpler components and then combining these components while preserving certain geometric properties.

### Dependencies
#### Theorems
* `RIGHT_IMP_EXISTS_THM`
* `SKOLEM_THM`
* `LEFT_IMP_EXISTS_THM`
* `FORALL_IN_UNIONS`
* `IMP_CONJ`
* `RIGHT_FORALL_IMP_THM`
* `FORALL_IN_IMAGE`
* `IN_UNIONS`
* `IN_ELIM_THM`
#### Definitions
* `hyperplane_cellcomplex`
* `UNIONS`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how these systems handle existential quantification and the introduction of functions like `f`. Additionally, the tactic scripts may need to be significantly restructured to match the native proof assistant's style, particularly in how they handle `GEN_REWRITE_TAC` and similar constructs. Differences in how unions and images are handled may also require careful consideration.

---

## HYPERPLANE_CELLCOMPLEX_UNION

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_UNION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_UNION = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY])
```

### Informal statement
For all sets A and all s and t, if A is a hyperplane cell complex of s and A is a hyperplane cell complex of t, then A is a hyperplane cell complex of the union of s and t.

### Informal sketch
* Start with the assumption that `A` is a `hyperplane_cellcomplex` of `s` and `t`.
* Use the definition of `hyperplane_cellcomplex` to understand the properties of `A` with respect to `s` and `t`.
* Apply the `HYPERPLANE_CELLCOMPLEX_UNIONS` theorem to establish that `A` is a `hyperplane_cellcomplex` of the union of `s` and `t`.
* Utilize the `UNIONS_2` property to handle the union of `s` and `t`.
* Apply `FORALL_IN_INSERT` and `NOT_IN_EMPTY` to ensure that the resulting complex satisfies the conditions for being a `hyperplane_cellcomplex`.

### Mathematical insight
This theorem provides a way to combine two cell complexes that are both hyperplane cell complexes with respect to the same set `A`, resulting in a new cell complex that is also a hyperplane cell complex with respect to `A`. This is useful in geometric and topological contexts where cell complexes are used to represent and analyze spaces.

### Dependencies
* Theorems:
  + `HYPERPLANE_CELLCOMPLEX_UNIONS`
* Definitions:
  + `hyperplane_cellcomplex`
  + `UNIONS_2`
  + `FORALL_IN_INSERT`
  + `NOT_IN_EMPTY`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of set unions and the properties of cell complexes. The `REPEAT STRIP_TAC` and `MATCH_MP_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `ASM_REWRITE_TAC` tactic may require manual rewriting of the terms using the `FORALL_IN_INSERT` and `NOT_IN_EMPTY` properties.

---

## HYPERPLANE_CELLCOMPLEX_UNIV

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_UNIV

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_UNIV = prove
 (`!A. hyperplane_cellcomplex A (:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_HYPERPLANE_CELLS] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
  REWRITE_TAC[IN_ELIM_THM; HYPERPLANE_CELL_CELLCOMPLEX]);;
```

### Informal statement
For all sets A, A is a hyperplane cell complex in the space of real numbers raised to the power of N.

### Informal sketch
* The proof starts by assuming an arbitrary set A and aiming to show it is a hyperplane cell complex in `:real^N`.
* The `REPEAT STRIP_TAC` suggests stripping away any universal quantifiers to work directly with the set A.
* The `REWRITE_TAC[GSYM UNIONS_HYPERPLANE_CELLS]` indicates rewriting the goal using the symmetric version of a theorem about unions of hyperplane cells, potentially to express A in terms of its components or to align with known properties of hyperplane cell complexes.
* The `MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS` applies a theorem that likely establishes conditions under which a union of sets forms a hyperplane cell complex, aiming to show A meets these conditions.
* Finally, `REWRITE_TAC[IN_ELIM_THM; HYPERPLANE_CELL_CELLCOMPLEX]` rewrites the goal using elimination theorems and properties of hyperplane cell complexes, possibly to finalize the proof by demonstrating that A satisfies the definition of a hyperplane cell complex.

### Mathematical insight
This theorem is important because it provides a condition or a characteristic that applies to all sets A in the context of hyperplane cell complexes within `:real^N`. It suggests a universal property of these mathematical objects, potentially simplifying or enabling further reasoning about their structure and behavior.

### Dependencies
* Theorems:
  - `HYPERPLANE_CELLCOMPLEX_UNIONS`
  - `UNIONS_HYPERPLANE_CELLS`
  - `IN_ELIM_THM`
  - `HYPERPLANE_CELL_CELLCOMPLEX`
* Definitions:
  - `hyperplane_cellcomplex`
  - `:real^N`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles universal quantification, set theory, and geometric concepts like hyperplane cell complexes. The `REPEAT STRIP_TAC` and `MATCH_MP_TAC` might be directly translated or require manual unfolding of the quantifiers and application of the relevant theorems. Additionally, the `REWRITE_TAC` steps may involve using rewrite engines or tacticals specific to the target proof assistant to apply the necessary theorems and definitions.

---

## HYPERPLANE_CELLCOMPLEX_INTERS

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_INTERS

### Type of the formal statement
Theorem

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
  CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]])
```

### Informal statement
For all sets $A$ and all collections $C$ of subsets of $\mathbb{R}^N$, if for every subset $s$ in $C$, $s$ is a hyperplane cell complex with respect to $A$, then the intersection of all subsets in $C$ is also a hyperplane cell complex with respect to $A$.

### Informal sketch
* The proof starts by considering the case where $C$ is empty, in which case the intersection of $C$ is the universe, and `HYPERPLANE_CELLCOMPLEX_UNIV` is used.
* A lemma is proved to show that the union of a set of sets is equal to the union of the non-empty sets in the set.
* The main proof involves assuming that $C$ is non-empty and using `GEN_REWRITE_TAC` and `REWRITE_TAC` to rewrite the statement in terms of `hyperplane_cellcomplex`.
* The `SKOLEM_THM` and `LEFT_IMP_EXISTS_THM` are used to introduce a function `f` that helps in rewriting the statement.
* The proof then proceeds by using `MATCH_MP_TAC` to apply `HYPERPLANE_CELLCOMPLEX_UNIONS`, `HYPERPLANE_CELL_CELLCOMPLEX`, and `HYPERPLANE_CELL_INTERS` to establish the result.
* The `CONJ_TAC` and `ASM_MESON_TAC` are used to conclude the proof.

### Mathematical insight
This theorem is important because it shows that the intersection of hyperplane cell complexes is also a hyperplane cell complex, which is a fundamental property in geometric and topological studies. The proof relies on the definition of `hyperplane_cellcomplex` and uses various tactics to manipulate the statement and apply relevant theorems.

### Dependencies
* `HYPERPLANE_CELLCOMPLEX_UNIV`
* `UNIONS_GSPEC`
* `EXTENSION`
* `IN_UNIONS`
* `IN_ELIM_THM`
* `NOT_IN_EMPTY`
* `HYPERPLANE_CELLCOMPLEX_UNIONS`
* `HYPERPLANE_CELL_CELLCOMPLEX`
* `HYPERPLANE_CELL_INTERS`
* `SKOLEM_THM`
* `LEFT_IMP_EXISTS_THM`
* `RIGHT_IMP_EXISTS_THM`

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the `hyperplane_cellcomplex` definition and the `INTERS` and `UNIONS` operations are correctly translated. Additionally, the use of `GEN_REWRITE_TAC` and `MATCH_MP_TAC` may need to be adapted to the target proof assistant's tactic language.

---

## HYPERPLANE_CELLCOMPLEX_INTER

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_INTER

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_INTER = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY])
```

### Informal statement
For all sets `A`, `s`, and `t`, if `A` is a hyperplane cell complex of `s` and `A` is a hyperplane cell complex of `t`, then `A` is a hyperplane cell complex of the intersection of `s` and `t`.

### Informal sketch
* The proof starts by assuming `hyperplane_cellcomplex A s` and `hyperplane_cellcomplex A t` for some sets `A`, `s`, and `t`.
* It then applies `REPEAT STRIP_TAC` to simplify the assumptions.
* Next, it uses `REWRITE_TAC` with `GSYM INTERS_2` to rewrite the intersection of `s` and `t`.
* The `MATCH_MP_TAC` tactic is applied with `HYPERPLANE_CELLCOMPLEX_INTERS` to establish the relationship between `A` and the intersection of `s` and `t`.
* Finally, `ASM_REWRITE_TAC` is used with `FORALL_IN_INSERT` and `NOT_IN_EMPTY` to conclude the proof.

### Mathematical insight
This theorem provides a way to compose hyperplane cell complexes. It states that if a set `A` is a hyperplane cell complex of two sets `s` and `t`, then it is also a hyperplane cell complex of their intersection. This is useful in geometric and topological contexts where cell complexes are used to represent and analyze spaces.

### Dependencies
* Theorems:
	+ `HYPERPLANE_CELLCOMPLEX_INTERS`
* Definitions:
	+ `hyperplane_cellcomplex`
	+ `INTER`
* Axioms and rules:
	+ `FORALL_IN_INSERT`
	+ `NOT_IN_EMPTY`

### Porting notes
When porting this theorem to another proof assistant, note that the `REPEAT STRIP_TAC` and `MATCH_MP_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `REWRITE_TAC` and `ASM_REWRITE_TAC` tactics may require different syntax or options to achieve the same effect. The `HYPERPLANE_CELLCOMPLEX_INTERS` theorem and `FORALL_IN_INSERT` and `NOT_IN_EMPTY` definitions will also need to be ported or defined in the target system.

---

## HYPERPLANE_CELLCOMPLEX_COMPL

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_COMPL

### Type of the formal statement
Theorem

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
    ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX; IN_ELIM_THM]])
```

### Informal statement
For all sets $A$ and $s$, if $A$ is a hyperplane cell complex of $s$, then $A$ is also a hyperplane cell complex of the complement of $s$ in $\mathbb{R}^N$. This statement is expressed as $\forall A \, s. \, \text{hyperplane\_cellcomplex} \, A \, s \implies \text{hyperplane\_cellcomplex} \, A \, ((\mathbb{R}^N) \setminus s)$.

### Informal sketch
* The proof starts by assuming $\text{hyperplane\_cellcomplex} \, A \, s$ and applying the definition of `hyperplane_cellcomplex` using `GEN_REWRITE_TAC`.
* It then proceeds to show that the complement of $s$ in $\mathbb{R}^N$ can be represented as the union of hyperplane cells of $A$, leveraging `HYPERPLANE_CELLCOMPLEX_INTERS` and properties of set complement and union.
* Key steps involve manipulating the representation of the complement of $s$ using `UNIONS_HYPERPLANE_CELLS`, handling the case where a cell $c$ is not equal to another cell $c'$ using `DISJOINT_HYPERPLANE_CELLS_EQ`, and applying `HYPERPLANE_CELLCOMPLEX_UNIONS` to conclude the proof.
* The use of `X_GEN_TAC` and `SUBGOAL_THEN` tactics indicates the introduction of new variables and the establishment of intermediate goals, respectively, to structure the proof.

### Mathematical insight
This theorem provides insight into the relationship between a hyperplane cell complex and its complement, showing that the complex's structure is preserved under complementation. This property is essential in geometric and topological contexts, where understanding the behavior of sets and their complements is crucial. The theorem's importance lies in its ability to facilitate reasoning about the geometric and topological properties of hyperplane cell complexes.

### Dependencies
#### Theorems
* `HYPERPLANE_CELLCOMPLEX_INTERS`
* `HYPERPLANE_CELLCOMPLEX_UNIONS`
* `DISJOINT_HYPERPLANE_CELLS_EQ`
#### Definitions
* `hyperplane_cellcomplex`
* `hyperplane_cell`
* `UNIONS_HYPERPLANE_CELLS`

---

## HYPERPLANE_CELLCOMPLEX_DIFF

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_DIFF

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_DIFF = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s DIFF t)`,
  ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
  SIMP_TAC[HYPERPLANE_CELLCOMPLEX_COMPL; HYPERPLANE_CELLCOMPLEX_INTER])
```

### Informal statement
For all sets A, s, and t, if A is a hyperplane cell complex of s and A is a hyperplane cell complex of t, then A is a hyperplane cell complex of the difference between s and t.

### Informal sketch
* The proof starts by assuming `hyperplane_cellcomplex A s` and `hyperplane_cellcomplex A t`.
* It then rewrites the difference `s DIFF t` as the intersection `s INTER (UNIV DIFF t)`, utilizing the `SET_RULE`.
* The proof proceeds by applying `SIMP_TAC` with `HYPERPLANE_CELLCOMPLEX_COMPL` and `HYPERPLANE_CELLCOMPLEX_INTER` to establish that `hyperplane_cellcomplex A (s DIFF t)` holds.
* The key steps involve leveraging the properties of set difference and intersection in relation to hyperplane cell complexes, specifically how these operations preserve the `hyperplane_cellcomplex` property.

### Mathematical insight
This theorem provides a way to reason about the difference of two sets in the context of hyperplane cell complexes. It is essential for constructing and manipulating geometric objects, as it allows for the combination of cell complexes while preserving their geometric properties. The theorem's importance lies in its ability to ensure that the resulting set from the difference operation still satisfies the conditions of being a hyperplane cell complex, which is crucial for maintaining the integrity of geometric constructions.

### Dependencies
* `hyperplane_cellcomplex`
* `SET_RULE`
* `HYPERPLANE_CELLCOMPLEX_COMPL`
* `HYPERPLANE_CELLCOMPLEX_INTER`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles set operations and geometric properties. Specifically, ensure that the equivalent of `SET_RULE` for rewriting set difference and the properties `HYPERPLANE_CELLCOMPLEX_COMPL` and `HYPERPLANE_CELLCOMPLEX_INTER` are correctly defined and applied. Additionally, consider the automation mechanisms available in the target system, as direct translation of `ONCE_REWRITE_TAC` and `SIMP_TAC` might not be straightforward.

---

## HYPERPLANE_CELLCOMPLEX_MONO

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_MONO

### Type of the formal statement
Theorem

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
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN ASM SET_TAC[]])
```

### Informal statement
For all sets `A` and `B` of type `real^N->bool` and for all `s`, if `A` is a hyperplane cell complex with respect to `s` and `A` is a subset of `B`, then `B` is also a hyperplane cell complex with respect to `s`.

### Informal sketch
* The proof begins by assuming `A` is a `hyperplane_cellcomplex` and `A SUBSET B`.
* It then applies `GEN_REWRITE_RULE` to rewrite `hyperplane_cellcomplex` using its definition.
* The proof proceeds by `DISCH_THEN` assuming a condition `C` related to `hyperplane_cellcomplex` and using `MATCH_MP_TAC` with `HYPERPLANE_CELLCOMPLEX_UNIONS` to establish a key property about unions of hyperplane cells.
* It uses `EXISTS_TAC` to introduce a set that helps in proving `B` is a `hyperplane_cellcomplex`, leveraging properties of `hyperplane_cell` and set operations like `UNION` and `INTER`.
* The proof involves several steps of rewriting, using `ASM_REWRITE_TAC` and `GEN_REWRITE_TAC`, to manipulate the expressions and apply relevant theorems like `UNIONS_HYPERPLANE_CELLS`.
* Key steps involve showing that certain sets satisfy the `hyperplane_cell` property and using `CONJ_TAC` to combine multiple conditions.

### Mathematical insight
This theorem provides a monotonicity property for hyperplane cell complexes, which is crucial in geometric and topological arguments. It ensures that if a set `A` is a hyperplane cell complex and is contained in another set `B`, then `B` also forms a hyperplane cell complex under the same conditions. This property is foundational in proving more complex results about the structure and behavior of geometric objects defined by hyperplane cell complexes.

### Dependencies
#### Theorems
* `HYPERPLANE_CELLCOMPLEX_UNIONS`
* `UNIONS_HYPERPLANE_CELLS`
#### Definitions
* `hyperplane_cellcomplex`
* `hyperplane_cell`

---

## FINITE_HYPERPLANE_CELLCOMPLEXES

### Name of formal statement
FINITE_HYPERPLANE_CELLCOMPLEXES

### Type of the formal statement
Theorem

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
For all sets A, if A is finite, then the set of all hyperplane cell complexes c (where c is a function from real^N to bool) such that c is a hyperplane cell complex of A, is also finite.

### Informal sketch
* The proof starts by assuming a finite set A and aiming to show the finiteness of the set of hyperplane cell complexes of A.
* It applies the `FINITE_SUBSET` theorem to establish that the set of hyperplane cell complexes is finite if it is a subset of a finite set.
* The `IMAGE` and `UNIONS` functions are used to construct a set that contains all possible unions of subsets of hyperplane cells of A, which is then shown to be finite using `FINITE_IMAGE` and `FINITE_POWERSET`.
* The `FINITE_HYPERPLANE_CELLS` theorem is also used to establish the finiteness of the set of hyperplane cells of A.
* The proof involves simplification and rewriting using `ASM_SIMP_TAC` and `REWRITE_TAC` to apply the definitions of `SUBSET`, `IN_IMAGE`, `IN_ELIM_THM`, and `hyperplane_cellcomplex`.
* The final step uses `MESON_TAC` to derive the conclusion from the established facts.

### Mathematical insight
This theorem provides a fundamental property of hyperplane cell complexes, which are geometric objects defined by a set of hyperplanes. The finiteness of the set of hyperplane cell complexes for a finite set A has implications for computational geometry and geometric reasoning. The proof relies on the finiteness of the set of hyperplane cells and the fact that the set of hyperplane cell complexes can be constructed as a finite union of subsets of these cells.

### Dependencies
* Theorems:
  * `FINITE_SUBSET`
  * `FINITE_IMAGE`
  * `FINITE_POWERSET`
  * `FINITE_HYPERPLANE_CELLS`
* Definitions:
  * `hyperplane_cell`
  * `hyperplane_cellcomplex`
  * `SUBSET`
  * `IN_IMAGE`
  * `IN_ELIM_THM`

### Porting notes
When translating this theorem to another proof assistant, special attention should be paid to the handling of `IMAGE` and `UNIONS` functions, as well as the `FINITE_SUBSET` theorem. The `MESON_TAC` tactic may need to be replaced with a similar tactic or a manual proof step, depending on the target system's automation capabilities. Additionally, the definitions of `hyperplane_cell` and `hyperplane_cellcomplex` should be carefully translated to ensure that the geometric intuition is preserved.

---

## FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES

### Name of formal statement
FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES

### Type of the formal statement
Theorem

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
For all predicates `P` and sets `A`, if `A` is finite, then the set of all functions `c` from `real^N` to `bool` such that `c` is a hyperplane cell complex of `A` and `P(c)` holds is finite.

### Informal sketch
* The proof starts by assuming a finite set `A` and a predicate `P`.
* It then aims to show that the set of functions `c` that are hyperplane cell complexes of `A` and satisfy `P(c)` is finite.
* The `FINITE_SUBSET` theorem is used to establish this finiteness by showing that the set of such functions is a subset of the set of all hyperplane cell complexes of `A`, which is known to be finite by `FINITE_HYPERPLANE_CELLCOMPLEXES`.
* The use of `REPEAT STRIP_TAC`, `MATCH_MP_TAC`, `EXISTS_TAC`, `ASM_SIMP_TAC`, and `SET_TAC` indicates a strategy of simplifying the goal, applying relevant theorems, and constructing the necessary sets and functions to prove the finiteness claim.

### Mathematical insight
This theorem provides a way to ensure the finiteness of a set of functions that satisfy certain properties related to hyperplane cell complexes, given that the underlying set `A` is finite. This is important in mathematical constructions and proofs that rely on the finiteness of such sets, particularly in geometric and topological contexts.

### Dependencies
* **Theorems:**
  - `FINITE_SUBSET`
  - `FINITE_HYPERPLANE_CELLCOMPLEXES`
* **Definitions:**
  - `hyperplane_cellcomplex` 

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to the handling of the `FINITE` predicate, the `hyperplane_cellcomplex` definition, and the `P` predicate. The use of `REPEAT STRIP_TAC` and `MATCH_MP_TAC` may need to be adapted based on the target system's tactic language and automation capabilities. Additionally, the representation of sets of functions from `real^N` to `bool` and the application of `FINITE_SUBSET` may require careful consideration of the target system's support for function types and subset relations.

---

## FINITE_SET_OF_HYPERPLANE_CELLS

### Name of formal statement
FINITE_SET_OF_HYPERPLANE_CELLS

### Type of the formal statement
Theorem

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
For all sets A and C, if A is finite and for every function c from real^N to bool that belongs to C, c is a hyperplane cell complex of A, then C is finite.

### Informal sketch
* The proof starts by assuming `FINITE A` and a set C such that every `c` in C satisfies `hyperplane_cellcomplex A c`.
* It then applies `FINITE_SUBSET` to show that C is finite by demonstrating it is a subset of a finite set.
* The `EXISTS_TAC` tactic is used to exhibit a set that contains all `c` such that `hyperplane_cellcomplex A c`, which is then shown to be finite using `FINITE_HYPERPLANE_CELLCOMPLEXES`.
* The `ASM_SIMP_TAC` and `ASM SET_TAC` are used to simplify and finalize the proof, ensuring the conclusion that C is finite.

### Mathematical insight
This theorem provides a condition under which a set of hyperplane cell complexes is finite, given that the underlying set A is finite. It's crucial for ensuring that certain constructions in geometric and topological contexts remain within finite and manageable bounds.

### Dependencies
* `FINITE_SUBSET`
* `FINITE_HYPERPLANE_CELLCOMPLEXES`
* `hyperplane_cellcomplex`

### Porting notes
When translating this into another proof assistant, pay special attention to how `FINITE` and `hyperplane_cellcomplex` are defined and used, as different systems may handle finiteness and geometric concepts differently. Additionally, the use of `REPEAT STRIP_TAC`, `MATCH_MP_TAC`, `EXISTS_TAC`, `ASM_SIMP_TAC`, and `ASM SET_TAC` may need to be adapted based on the target system's tactic language and automation capabilities.

---

## CELL_SUBSET_CELLCOMPLEX

### Name of formal statement
CELL_SUBSET_CELLCOMPLEX

### Type of the formal statement
Theorem

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
    ASM_MESON_TAC[]])
```

### Informal statement
For all sets `A` and `s` and all cells `c` in `real^N->bool`, if `c` is a hyperplane cell of `A` and `s` is a hyperplane cell complex of `A`, then `c` is a subset of `s` if and only if `c` and `s` are not disjoint.

### Informal sketch
* The proof starts by assuming `c` is a hyperplane cell of `A` and `s` is a hyperplane cell complex of `A`.
* It then considers two cases: when `c` is empty and when `c` is not empty.
* If `c` is empty, the statement is proven using `NONEMPTY_HYPERPLANE_CELL`.
* If `c` is not empty, the proof involves rewriting `DISJOINT` and `UNIONS` using `GSYM MEMBER_NOT_EMPTY`, `UNIONS_GSPEC`, `IN_ELIM_THM`, and `LEFT_IMP_EXISTS_THM`.
* The proof then uses `DISJOINT_HYPERPLANE_CELLS_EQ` to establish a relationship between `c` and `s`.
* Finally, the proof applies `SET_RULE` to show that `c` is a subset of `s` if and only if `c` and `s` are not disjoint.
* Key steps involve using `REPEAT STRIP_TAC`, `FIRST_ASSUM`, `DISCH_THEN`, `EQ_TAC`, `ASM_CASES_TAC`, `REWRITE_TAC`, `MAP_EVERY X_GEN_TAC`, and `MATCH_MP_TAC` to structure the proof.

### Mathematical insight
This theorem provides a condition for a cell to be a subset of a cell complex, which is crucial in geometric and topological contexts. The `hyperplane_cell` and `hyperplane_cellcomplex` definitions are fundamental in describing geometric objects, and this theorem helps in understanding their relationships.

### Dependencies
* `hyperplane_cell`
* `hyperplane_cellcomplex`
* `DISJOINT`
* `NONEMPTY_HYPERPLANE_CELL`
* `DISJOINT_HYPERPLANE_CELLS_EQ`
* `SET_RULE`
* `UNIONS_GSPEC`
* `IN_ELIM_THM`
* `LEFT_IMP_EXISTS_THM`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of binders, especially in the `GEN_REWRITE_RULE` and `X_GEN_TAC` steps. Additionally, the `REPEAT STRIP_TAC` and `EQ_TAC` tactics may need to be replaced with equivalent tactics in the target system. The `DISJOINT_HYPERPLANE_CELLS_EQ` theorem and `SET_RULE` may also require special attention due to their specific mathematical content.

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
            (\c. (-- &1) pow (num_of_int(aff_dim c)))`
```

### Informal statement
The Euler characteristic of a set `s` with respect to `A` is defined as the sum over all cells `c` such that `c` is a hyperplane cell of `A` and `c` is a subset of `s`, of the value `(-1)` raised to the power of the affine dimension of `c`.

### Informal sketch
* The definition involves a summation over cells `c` that satisfy two conditions: being a `hyperplane_cell` of `A` and being a subset of `s`.
* For each such cell `c`, the term `(-- &1) pow (num_of_int(aff_dim c))` is evaluated, which involves calculating the affine dimension of `c` using `aff_dim c`, converting this dimension to an integer with `num_of_int`, and then raising `-1` to this power.
* The `sum` function then adds up these terms for all qualifying cells `c`.

### Mathematical insight
The Euler characteristic is a fundamental concept in topology and geometry, capturing a property of a space that remains invariant under certain transformations. This definition specifically applies to a set `s` within a structure `A`, considering the contributions of hyperplane cells and their dimensions to the overall characteristic.

### Dependencies
* `hyperplane_cell`
* `aff_dim`
* `num_of_int`
* `sum`

### Porting notes
When translating this definition into another proof assistant, pay close attention to how the target system handles set comprehensions, summations, and the interaction between logical and arithmetic operations. Specifically, ensure that the equivalent of `sum` correctly handles the set of cells `c` that meet the given conditions, and that the power operation is correctly applied to `-1` with the dimension of `c` as the exponent. Additionally, verify that the `hyperplane_cell` and `aff_dim` concepts are appropriately defined or imported in the target system.

---

## EULER_CHARACTERISTIC_EMPTY

### Name of formal statement
EULER_CHARACTERISTIC_EMPTY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_EMPTY = prove
 (`euler_characteristic A {} = &0`,
  REWRITE_TAC[euler_characteristic; SUBSET_EMPTY] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN
  MATCH_MP_TAC(MESON[] `~(?x. x IN s) ==> (!x. x IN s ==> P x)`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[NONEMPTY_HYPERPLANE_CELL])
```

### Informal statement
The Euler characteristic of the empty set is equal to 0.

### Informal sketch
* The proof begins by applying the `euler_characteristic` definition and the `SUBSET_EMPTY` property to simplify the expression `euler_characteristic A {}`.
* It then uses `MATCH_MP_TAC` with `SUM_EQ_0` to establish that the sum of an empty set is 0.
* The `MESON` tactic is applied with the premise that if no element exists in a set `s`, then for all `x` in `s`, any property `P` holds (vacuously), which is used to handle the empty set case.
* The `IN_ELIM_THM` is used to eliminate the membership condition for the empty set, and finally, `MESON_TAC` with `NONEMPTY_HYPERPLANE_CELL` is applied to conclude the proof.

### Mathematical insight
This theorem provides a basic property of the Euler characteristic, which is a fundamental concept in topology. The Euler characteristic of a space is a topological invariant that can be used to distinguish between non-homeomorphic spaces. The fact that the Euler characteristic of the empty set is 0 reflects the idea that the empty set has no "holes" or "voids" in a topological sense.

### Dependencies
* Theorems:
  * `SUM_EQ_0`
  * `SUBSET_EMPTY`
  * `IN_ELIM_THM`
  * `NONEMPTY_HYPERPLANE_CELL`
* Definitions:
  * `euler_characteristic` 

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles the Euler characteristic, empty sets, and the specific tactics used (e.g., `REWRITE_TAC`, `MATCH_MP_TAC`, `MESON_TAC`). The main challenge will be to find equivalent tactics or strategies in the target system that can replicate the logical flow of the HOL Light proof.

---

## EULER_CHARACTERISTIC_CELL_UNIONS

### Name of formal statement
EULER_CHARACTERISTIC_CELL_UNIONS

### Type of the formal statement
Theorem

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
   [ASM SET_TAC[]; ASM_MESON_TAC[DISJOINT_HYPERPLANE_CELLS_EQ]])
```

### Informal statement
For all sets $A$ and collections $C$ of hyperplane cells, if every cell $c$ in $C$ is a hyperplane cell of $A$, then the Euler characteristic of $A$ with respect to the union of cells in $C$ is equal to the sum over all cells $c$ in $C$ of $(-1)$ raised to the power of the affine dimension of $c$.

### Informal sketch
* The proof starts by assuming that every cell $c$ in $C$ is a hyperplane cell of $A$.
* It then uses the `euler_characteristic` definition and applies `REWRITE_TAC` to transform the goal into a sum over the cells in $C$.
* The `MATCH_MP_TAC` tactic is used with a lemma stating that the sum of a function over two equal sets is equal, allowing the proof to proceed with equating the sums.
* The `X_GEN_TAC` and `EQ_TAC` tactics are used to introduce a new variable $c$ and split the equality into two separate goals.
* The proof then proceeds by cases, using `DISCH_THEN` and `CONJUNCTS_THEN2` to handle the assumptions and conclusions.
* The `SUBGOAL_THEN` tactic is used to introduce a new subgoal, which is then solved using `ASM_MESON_TAC` and `NONEMPTY_HYPERPLANE_CELL`.
* The `REWRITE_TAC` and `GSYM` tactics are used to apply various definitions and properties, including `MEMBER_NOT_EMPTY`, `SUBSET`, and `IN_UNIONS`.
* The `X_GEN_TAC` and `DISCH_TAC` tactics are used to introduce a new variable $x$ and discharge assumptions.
* The `DISCH_THEN` and `MP_TAC` tactics are used to apply the `SPEC` tactic and introduce a new assumption.
* The `ASM_REWRITE_TAC` tactic is used to apply various definitions and properties.
* The `DISCH_THEN` and `X_CHOOSE_THEN` tactics are used to introduce a new variable $c'$ and apply the `STRIP_ASSUME_TAC` tactic.
* The `SUBGOAL_THEN` tactic is used to introduce a new subgoal, which is then solved using `ASM_MESON_TAC` and `DISJOINT_HYPERPLANE_CELLS_EQ`.

### Mathematical insight
The Euler characteristic is a fundamental invariant in topology, and this theorem provides a way to compute it for a union of hyperplane cells. The key idea is to use the additivity of the Euler characteristic and the fact that the Euler characteristic of a hyperplane cell is $(-1)$ raised to the power of its affine dimension.

### Dependencies
* `euler_characteristic`
* `hyperplane_cell`
* `UNIONS`
* `aff_dim`
* `NONEMPTY_HYPERPLANE_CELL`
* `DISJOINT_HYPERPLANE_CELLS_EQ`
* `MEMBER_NOT_EMPTY`
* `SUBSET`
* `IN_UNIONS`
* `GSYM`
* `LEFT_IMP_EXISTS_THM`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `euler_characteristic` definition and the `hyperplane_cell` predicate are defined and used correctly. Additionally, the `REPEAT` and `STRIP_TAC` tactics may need to be replaced with equivalent tactics in the target system. The use of `X_GEN_TAC` and `DISCH_TAC` may also require special attention, as these tactics are used to introduce and discharge assumptions in a way that is specific to HOL Light.

---

## EULER_CHARACTERISTIC_CELL

### Name of formal statement
EULER_CHARACTERISTIC_CELL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_CELL = prove
 (`!A c. hyperplane_cell A c
         ==> euler_characteristic A c = (-- &1) pow (num_of_int(aff_dim c))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM UNIONS_1] THEN
  ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELL_UNIONS; IN_SING; SUM_SING])
```

### Informal statement
For all sets `A` and cells `c`, if `c` is a hyperplane cell of `A`, then the Euler characteristic of `A` with respect to `c` is equal to `(-1)` raised to the power of the dimension of the affine space of `c`.

### Informal sketch
* The proof starts by assuming `c` is a hyperplane cell of `A`.
* It then applies `REPEAT STRIP_TAC` to strip away the universal quantifier and implication.
* Next, `GEN_REWRITE_TAC` is applied with `GSYM UNIONS_1` to rewrite the `UNIONS_1` theorem in a suitable form for the current context.
* The proof then uses `ASM_SIMP_TAC` with `EULER_CHARACTERISTIC_CELL_UNIONS`, `IN_SING`, and `SUM_SING` to simplify the expression involving the Euler characteristic.
* The `EULER_CHARACTERISTIC_CELL_UNIONS` theorem likely provides a relationship between the Euler characteristic and unions of cells, which is crucial for simplifying the expression.
* The `IN_SING` and `SUM_SING` theorems probably deal with properties of singleton sets and sums, respectively, which are used to further simplify the expression.

### Mathematical insight
The Euler characteristic is a fundamental concept in topology, and this theorem provides a relationship between the Euler characteristic of a set and the dimension of its affine space. This is likely a crucial step in establishing more complex topological results, and understanding this relationship can provide insight into the structure of the set.

### Dependencies
* Theorems:
  + `EULER_CHARACTERISTIC_CELL_UNIONS`
  + `IN_SING`
  + `SUM_SING`
  + `UNIONS_1`
* Definitions:
  + `euler_characteristic`
  + `hyperplane_cell`
  + `aff_dim`

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the `REPEAT STRIP_TAC` and `GEN_REWRITE_TAC` tactics are properly replaced with equivalent tactics in the target system. Additionally, the `EULER_CHARACTERISTIC_CELL_UNIONS`, `IN_SING`, and `SUM_SING` theorems will need to be ported or re-proved in the target system. The use of `ASM_SIMP_TAC` may also require special attention, as the simplification tactics and theorems used may differ between systems.

---

## EULER_CHARACTERISTIC_CELLCOMPLEX_UNION

### Name of formal statement
EULER_CHARACTERISTIC_CELLCOMPLEX_UNION

### Type of the formal statement
Theorem

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
    ASM_SIMP_TAC[HYPERPLANE_CELLCOMPLEX_UNION] THEN SET_TAC[]])
```

### Informal statement
For all sets `A`, `s`, and `t` from `real^N` to `bool`, if `A` is finite and both `s` and `t` are hyperplane cell complexes of `A`, and `s` and `t` are disjoint, then the Euler characteristic of `A` with respect to the union of `s` and `t` is equal to the sum of the Euler characteristics of `A` with respect to `s` and `t` individually.

### Informal sketch
* The proof starts by assuming the premises: `A` is finite, `s` and `t` are hyperplane cell complexes of `A`, and `s` and `t` are disjoint.
* It then applies `REWRITE_TAC` to express the `euler_characteristic` in terms of its definition, followed by `CONV_TAC SYM_CONV` for symmetry conversion.
* The `MATCH_MP_TAC SUM_UNION_EQ` tactic is used to apply the `SUM_UNION_EQ` theorem, which is crucial for establishing the relationship between the Euler characteristics of the union and the individual sets.
* Further simplifications and case analyses are performed using `ASM_SIMP_TAC`, `ASM_CASES_TAC`, and `ASM_REWRITE_TAC`, considering the properties of hyperplane cells and cell complexes.
* The proof involves showing that for any cell `c`, either `c` is empty or it is a hyperplane cell of `A`, and using `CELL_SUBSET_CELLCOMPLEX` to establish subset relationships.

### Mathematical insight
This theorem provides a way to compute the Euler characteristic of a cell complex that is the union of two disjoint cell complexes, by simply adding their individual Euler characteristics. This is a fundamental property in algebraic topology, useful for calculating topological invariants of spaces.

### Dependencies
#### Theorems
* `SUM_UNION_EQ`
* `CELL_SUBSET_CELLCOMPLEX`
#### Definitions
* `euler_characteristic`
* `hyperplane_cellcomplex`
* `DISJOINT`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to the handling of `real^N->bool` types and the `DISJOINT` predicate, as different systems may represent these concepts differently. Additionally, the tactic script may need adjustments due to variations in automation and tactic libraries across proof assistants.

---

## EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS

### Name of formal statement
EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS

### Type of the formal statement
Theorem

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
    ASM_REWRITE_TAC[pairwise] THEN ASM SET_TAC[]])
```

### Informal statement
For all finite sets $A$ and all sets of hyperplane cell complexes $C$ such that each $c \in C$ is a hyperplane cell complex in $A$, and $C$ is pairwise disjoint, the Euler characteristic of the union of $C$ in $A$ is equal to the sum of the Euler characteristics of each $c \in C$ in $A$.

### Informal sketch
* The proof starts by assuming the finiteness of $A$ and the pairwise disjointness of $C$.
* It then proceeds by strong induction on the finiteness of $C$, using `FINITE_INDUCT_STRONG`.
* The base case is handled by `EULER_CHARACTERISTIC_EMPTY`, `SUM_CLAUSES`, and `UNIONS_0`.
* For the inductive step, it uses `UNIONS_INSERT` and `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION` to reduce the problem to smaller instances.
* Key steps involve using `HYPERPLANE_CELLCOMPLEX_UNIONS`, `DISJOINT`, and `INTER_UNIONS` to establish the necessary properties for the inductive step.
* The proof concludes by showing that the Euler characteristic of the union of $C$ in $A$ equals the sum of the Euler characteristics of each $c \in C$ in $A$.

### Mathematical insight
This theorem provides a way to compute the Euler characteristic of a union of hyperplane cell complexes in a finite set $A$, by decomposing it into the sum of the Euler characteristics of the individual cell complexes, under the condition that these complexes are pairwise disjoint. This is a fundamental property in algebraic topology and geometric combinatorics, facilitating the calculation of topological invariants in complex geometric configurations.

### Dependencies
#### Theorems
* `EULER_CHARACTERISTIC_EMPTY`
* `HYPERPLANE_CELLCOMPLEX_UNIONS`
* `FINITE_SET_OF_HYPERPLANE_CELLS`
#### Definitions
* `euler_characteristic`
* `hyperplane_cellcomplex`
* `UNIONS`
* `DISJOINT`
#### Inductive rules
* `FINITE_INDUCT_STRONG`

---

## EULER_CHARACTERISTIC

### Name of formal statement
EULER_CHARACTERISTIC

### Type of the formal statement
Theorem

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
    REWRITE_TAC[REAL_MUL_AC]])
```

### Informal statement
For all sets `A` of type `real^N->bool` and all subsets `s` of `real^N`, if `A` is finite, then the Euler characteristic of `A` restricted to `s` is equal to the sum over all dimensions `d` from 0 to `dimindex(:N)` of `(-1)^d` times the number of cells `c` in `A` that are subsets of `s` and have affine dimension `d`.

### Informal sketch
* The proof starts by assuming `A` is finite and then applies the `euler_characteristic` definition.
* It then uses `SUM_GROUP` to transform the sum over dimensions into a sum over the image of a function, which simplifies the expression.
* The proof proceeds by cases, using `ANTS_TAC` to split into two main branches:
  + The first branch uses `FINITE_RESTRICT_HYPERPLANE_CELLS` and properties of `aff_dim` to establish the existence of cells with certain properties.
  + The second branch uses `DISCH_THEN` and `SUBST1_TAC` to simplify the expression and then applies `SUM_CONST` and `FINITE_RESTRICT_HYPERPLANE_CELLS` to conclude the proof.
* Key HOL Light terms used include `euler_characteristic`, `SUM_GROUP`, `aff_dim`, and `FINITE_RESTRICT_HYPERPLANE_CELLS`.

### Mathematical insight
The Euler characteristic is a fundamental concept in topology, and this theorem provides a way to compute it for finite sets in `real^N` by summing over the dimensions of cells in the set. The use of `(-1)^d` in the sum reflects the alternating pattern of addition and subtraction in the Euler characteristic formula.

### Dependencies
* Theorems:
  + `SUM_GROUP`
  + `FINITE_RESTRICT_HYPERPLANE_CELLS`
  + `euler_characteristic`
* Definitions:
  + `aff_dim`
  + `hyperplane_cell`
  + `euler_characteristic`
* Other:
  + `REAL_MUL_AC`
  + `INT_OF_NUM_EQ`
  + `NUM_OF_INT_OF_NUM`
  + `o_DEF`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of finite sets and the `euler_characteristic` definition. The use of `SUM_GROUP` and `ANTS_TAC` may require equivalent tactics or rewriting rules in the target system. Additionally, the `aff_dim` and `hyperplane_cell` definitions may need to be adapted to the target system's representation of geometric objects.

---

## HYPERPLANE_CELLS_DISTINCT_LEMMA

### Name of formal statement
HYPERPLANE_CELLS_DISTINCT_LEMMA

### Type of the formal statement
Theorem

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
  REAL_ARITH_TAC)
```

### Informal statement
For all vectors `a` and all real numbers `b`, the following intersections are empty: the intersection of the hyperplane `{x | a dot x = b}` and the half-space `{x | a dot x < b}`, the intersection of the hyperplane `{x | a dot x = b}` and the half-space `{x | a dot x > b}`, the intersection of the half-space `{x | a dot x < b}` and the hyperplane `{x | a dot x = b}`, the intersection of the half-space `{x | a dot x < b}` and the half-space `{x | a dot x > b}`, the intersection of the half-space `{x | a dot x > b}` and the hyperplane `{x | a dot x = b}`, and the intersection of the half-space `{x | a dot x > b}` and the half-space `{x | a dot x < b}`.

### Informal sketch
* The proof involves showing that certain sets are disjoint by demonstrating their intersections are empty.
* It starts with a universal quantification over all vectors `a` and real numbers `b`.
* The `REWRITE_TAC` tactic is used with theorems `EXTENSION`, `IN_INTER`, `IN_ELIM_THM`, and `NOT_IN_EMPTY` to rewrite the goal in terms of set operations and membership.
* The `REAL_ARITH_TAC` tactic is then applied to simplify and solve the resulting arithmetic and set equality statements.
* Key steps involve recognizing that the dot product `a dot x` being equal to `b` cannot simultaneously be less than or greater than `b`, which underlies the emptiness of the intersections involving the hyperplane and the half-spaces.

### Mathematical insight
This lemma is important because it establishes a fundamental property about the relationship between hyperplanes and half-spaces in a geometric or vector space context. It shows that these geometric objects are distinct and do not overlap in certain ways, which is crucial for further geometric and topological constructions. The intuition is based on the understanding that a hyperplane divides the space into two half-spaces, and the points on the hyperplane itself do not belong to either half-space in the strict sense (less than or greater than).

### Dependencies
* Theorems:
  - `EXTENSION`
  - `IN_INTER`
  - `IN_ELIM_THM`
  - `NOT_IN_EMPTY`
  - `REAL_ARITH_TAC` (as a tactic, not a theorem, but crucial for the proof)
* Definitions:
  - `dot` (dot product operation)

### Porting notes
When translating this lemma into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how these systems handle set operations, real arithmetic, and the representation of geometric concepts like hyperplanes and half-spaces. The `REWRITE_TAC` and `REAL_ARITH_TAC` tactics may have counterparts or need to be emulated through a combination of tactics and automated reasoning tools available in the target system. Additionally, the formulation of the lemma and its proof might need adjustments to fit the specific logical framework and syntax of the target proof assistant.

---

## EULER_CHARACTERSTIC_LEMMA

### EULER_CHARACTERSTIC_LEMMA
- The exact name of the formal statement.

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let EULER_CHARACTERSTIC_LEMMA = prove
 (`!A h s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s
        ==> euler_characteristic (h INSERT A) s = euler_characteristic A s`,
  ... )
```

### Informal statement
For all sets `A` and `h` in `real^N->bool` and all `s` in `real^N->bool`, if `A` is finite and `A` is a hyperplane cell complex with respect to `s`, then the Euler characteristic of `h` inserted into `A` with respect to `s` is equal to the Euler characteristic of `A` with respect to `s`.

### Informal sketch
* The proof starts by assuming `A` is finite and `A` is a hyperplane cell complex with respect to `s`.
* It then proceeds to show that the Euler characteristic of `h` inserted into `A` with respect to `s` is equal to the Euler characteristic of `A` with respect to `s`.
* The proof uses various properties of hyperplane cell complexes, such as `HYPERPLANE_CELLCOMPLEX` and `HYPERPLANE_CELL_UNION`.
* It also employs tactics like `REWRITE_TAC`, `MAP_EVERY`, `DISCH_THEN`, and `MATCH_MP_TAC` to manipulate the expressions and apply relevant theorems.
* Key steps include:
 + Showing that `A` and `h INSERT A` have the same Euler characteristic with respect to `s`.
 + Using the `EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS` theorem to simplify the expression for the Euler characteristic of `h INSERT A`.
 + Applying the `HYPERPLANE_CELLS_DISTINCT_LEMMA` to establish a relationship between the hyperplane cells of `A` and `h INSERT A`.
* The proof concludes by demonstrating that the Euler characteristic of `h INSERT A` with respect to `s` is indeed equal to the Euler characteristic of `A` with respect to `s`.

### Mathematical insight
The Euler characteristic is a fundamental concept in topology, and this lemma provides insight into how it behaves under the insertion of a new element into a hyperplane cell complex. The result has implications for understanding the topological properties of such complexes and can be used to derive further results in algebraic topology.

### Dependencies
* Theorems:
 + `HYPERPLANE_CELLCOMPLEX`
 + `HYPERPLANE_CELL_UNION`
 + `EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS`
 + `HYPERPLANE_CELLS_DISTINCT_LEMMA`
* Definitions:
 + `hyperplane_cellcomplex`
 + `euler_characteristic`
 + `hyperplane_cell`

### Porting notes
When porting this lemma to other proof assistants, pay attention to the handling of binders and the representation of hyperplane cell complexes. The `HYPERPLANE_CELLCOMPLEX` and `EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS` theorems may require special attention due to their reliance on specific properties of hyperplane cell complexes. Additionally, the use of `REWRITE_TAC` and `MATCH_MP_TAC` tactics may need to be adapted to the target proof assistant's syntax and tactic language.

---

## EULER_CHARACTERSTIC_INVARIANT

### Name of formal statement
EULER_CHARACTERSTIC_INVARIANT

### Type of the formal statement
Theorem

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
    ASM_MESON_TAC[UNION_COMM]])
```

### Informal statement
For all sets A and B of type real^N->bool, if A and B are finite, and both are hyperplane cell complexes with respect to s, then the Euler characteristic of A with respect to s is equal to the Euler characteristic of B with respect to s.

### Informal sketch
* The proof involves assuming `FINITE A` and `FINITE B` and `hyperplane_cellcomplex A s` and `hyperplane_cellcomplex B s`, then showing `euler_characteristic A s = euler_characteristic B s`.
* It uses a subgoal that involves showing for any set A and any finite set B, `euler_characteristic (A UNION B) s = euler_characteristic A s`.
* The proof employs `FINITE_INDUCT_STRONG` for induction, `MATCH_MP_TAC` with `EULER_CHARACTERSTIC_LEMMA`, and `HYPERPLANE_CELLCOMPLEX_MONO` to establish the relationship between the Euler characteristics.
* Key steps include using `ASM_REWRITE_TAC` with `UNION_EMPTY` and `SET_RULE` for set manipulation, and `EXISTS_TAC` to introduce specific sets.
* The second part of the proof involves using `RULE_ASSUM_TAC` and `REWRITE_RULE` to manipulate assumptions and implications, followed by `MATCH_MP_TAC` with `EQ_TRANS` to establish equality.

### Mathematical insight
This theorem is important because it shows that the Euler characteristic, which is a topological invariant, remains the same for certain types of cell complexes (hyperplane cell complexes) under specific conditions (finite sets A and B). This has implications for understanding the topological properties of these cell complexes and their behavior under union operations.

### Dependencies
* Theorems:
  * `EULER_CHARACTERSTIC_LEMMA`
  * `FINITE_INDUCT_STRONG`
  * `HYPERPLANE_CELLCOMPLEX_MONO`
* Definitions:
  * `euler_characteristic`
  * `hyperplane_cellcomplex`
  * `FINITE`
* Inductive rules: 
  * `FINITE_INDUCT_STRONG`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to the handling of finite sets, the definition and properties of `euler_characteristic`, and the specific `hyperplane_cellcomplex` definition. The use of `SUBGOAL_THEN` and tactic combinations like `MATCH_MP_TAC` followed by `ASM_REWRITE_TAC` might require careful consideration due to differences in how tactics and automation are handled across systems.

---

## EULER_CHARACTERISTIC_INCLUSION_EXCLUSION

### Name of formal statement
EULER_CHARACTERISTIC_INCLUSION_EXCLUSION

### Type of the formal statement
Theorem

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
           HYPERPLANE_CELLCOMPLEX_UNION; HYPERPLANE_CELLCOMPLEX_DIFF])
```

### Informal statement
For all sets `A` and `s` of type `(real^N->bool)` such that `A` is finite, `s` is finite, and for all `k` in `s`, `k` is a `hyperplane_cellcomplex` of `A`, the Euler characteristic of `A` in the union of `s` is equal to the sum over all non-empty subsets `t` of `s` of `(-1)^(CARD t + 1)` times the Euler characteristic of `A` in the intersection of `t`.

### Informal sketch
* The proof starts by assuming the finiteness of `A` and `s`, and the property that every `k` in `s` is a `hyperplane_cellcomplex` of `A`.
* It then applies the `INCLUSION_EXCLUSION_REAL_RESTRICTED` theorem, which likely involves principles of inclusion-exclusion for sets.
* The `ASM_SIMP_TAC` and `SIMP_TAC` tactics are used to simplify the expression, leveraging properties of `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION` and various `HYPERPLANE_CELLCOMPLEX` definitions.
* Key steps involve recognizing the application of the inclusion-exclusion principle to calculate the Euler characteristic of the union of sets in `s`, and simplifying the resulting expression based on properties of Euler characteristics and set operations.

### Mathematical insight
This theorem provides a way to compute the Euler characteristic of a union of sets by considering the Euler characteristics of the sets and their intersections. The principle of inclusion-exclusion is crucial here, allowing for the calculation of the Euler characteristic of a union by summing over subsets and accounting for overcounting through the use of `(-1)^(CARD t + 1)`. This is important in algebraic topology for understanding the properties of spaces and their subspaces.

### Dependencies
* Theorems:
  + `INCLUSION_EXCLUSION_REAL_RESTRICTED`
  + `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION`
* Definitions:
  + `hyperplane_cellcomplex`
  + `euler_characteristic`
  + `UNIONS`
  + `INTERS`
  + `HYPERPLANE_CELLCOMPLEX_EMPTY`
  + `HYPERPLANE_CELLCOMPLEX_INTER`
  + `HYPERPLANE_CELLCOMPLEX_UNION`
  + `HYPERPLANE_CELLCOMPLEX_DIFF`

### Porting notes
When translating this into another proof assistant, pay special attention to how the target system handles finite sets, set operations (like union and intersection), and the principle of inclusion-exclusion. Additionally, ensure that the notion of Euler characteristic and its properties are defined and accessible in the target system. The use of `REPEAT STRIP_TAC`, `MP_TAC`, `ASM_SIMP_TAC`, and `SIMP_TAC` may need to be adapted based on the target system's tactic language and simplification mechanisms.

---

## EULER_POLYHEDRAL_CONE

### Name of formal statement
EULER_POLYHEDRAL_CONE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EULER_POLYHEDRAL_CONE = prove
 (`!s. polyhedron s /\ conic s /\ ~(interior s = {}) /\ ~(s = (:real^N))
       ==> sum (0..dimindex(:N))
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of s /\ aff_dim f = &d })) = &0`,
  ... )
```

### Informal statement
For all sets $s$, if $s$ is a polyhedron, $s$ is a cone, the interior of $s$ is not empty, and $s$ is not equal to $\mathbb{R}^N$, then the sum from $0$ to the dimension of $\mathbb{R}^N$ of $(-1)^d$ times the number of faces of $s$ with affine dimension $d$ is equal to $0$.

### Informal sketch
* The proof starts by assuming the conditions on $s$: it is a polyhedron, a cone, has non-empty interior, and is not the entire space $\mathbb{R}^N$.
* It then applies various properties and theorems related to polyhedra and cones, such as `CONIC_CONTAINS_0`, `POLYHEDRON_INTER_AFFINE_MINIMAL`, and `FACE_OF_REFL`, to derive key properties about $s$ and its faces.
* The proof involves using tactics like `STRIP_TAC`, `MATCH_MP_TAC`, and `GEN_REWRITE_TAC` to manipulate and simplify the expressions involving $s$ and its faces.
* It utilizes the concept of Euler characteristic and its relation to the number of faces of different dimensions in a polyhedron.
* The proof also employs the `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION` theorem to relate the Euler characteristic of $s$ to the sum of Euler characteristics of its faces.
* Through a series of logical deductions and applications of theorems, the proof ultimately shows that the given sum equals $0$.

### Mathematical insight
This theorem provides an Euler-type relation for full-dimensional proper polyhedral cones, relating the number of faces of different dimensions to the Euler characteristic of the cone. It is a fundamental result in the theory of polyhedra, highlighting the deep connection between the geometric and topological properties of these objects.

### Dependencies
* `CONIC_CONTAINS_0`
* `POLYHEDRON_INTER_AFFINE_MINIMAL`
* `FACE_OF_REFL`
* `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION`
* `HYPERPLANE_CELLCOMPLEX_MONO`
* `HYPERPLANE_CELL_CELLCOMPLEX`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of binders, the representation of polyhedra and cones, and the implementation of the Euler characteristic. The `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION` theorem, in particular, may require careful translation due to its reliance on specific properties of cell complexes and Euler characteristics. Additionally, the use of tactics like `GEN_REWRITE_TAC` and `MATCH_MP_TAC` may need to be adapted to the target system's tactic language.

---

## EULER_POINCARE_LEMMA

### Name of formal statement
EULER_POINCARE_LEMMA

### Type of the formal statement
Theorem

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
  EXISTS_TAC `\f:real^N->bool. f INTER {x:real^N | x$1 = &1}` THEN
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
   [REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `f:real^N->bool = {}` THENL
     [REWRITE_TAC[CONIC_HULL_EMPTY; EMPTY_FACE_OF] THEN
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
    SUBGOAL_THEN `(x:real^N) IN segment(a,b)` MP_TAC THENL
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
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC; IN_INSERT]]
```

### Informal statement
Let $p$ be an $(n-1)$-dimensional polytope in $\mathbb{R}^N$ such that $2 \leq \dimindex(\mathbb{R}^N)$ and the affine hull of $p$ is the hyperplane $\{x \in \mathbb{R}^N \mid x_1 = 1\}$. Then, for each $d = 0, 1, \ldots, n-1$, let $f_d$ be the set of $d$-dimensional faces of $p$. The following equation holds: $$\sum_{d=0}^{n-1} (-1)^d \cdot \#(f_d) = 1,$$ where $\#(f_d)$ denotes the number of $d$-dimensional faces of $p$.

### Informal sketch
The proof involves several main steps:
* Showing that $p$ is a polytope and its affine hull is a hyperplane
* Defining the conic hull $s$ of $p$ and establishing its properties
* Proving that $s$ is a polyhedron and $s \neq \mathbb{R}^N$
* Establishing a bijection between the faces of $p$ and the faces of $s$
* Using this bijection to relate the number of faces of $p$ to the number of faces of $s$
* Applying the Euler-Poincaré formula to $s$ to obtain the desired equation

Key concepts and theorems used in the proof include:
* Properties of polytopes and their faces
* Conic hulls and their properties
* Affine hulls and their properties
* The Euler-Poincaré formula for polyhedra
* Bijections and their role in establishing equalities between sets

### Mathematical insight
The Euler-Poincaré lemma provides a fundamental relationship between the number of faces of different dimensions in a polytope. This relationship is a consequence of the topological properties of polytopes and is a key ingredient in many proofs in geometry and topology. The lemma is often used in conjunction with other results, such as the Euler-Poincaré formula, to establish deeper properties of polytopes and other geometric objects.

### Dependencies
* `AFF_DIM_HYPERPLANE`
* `CONIC_HULL_EXPLICIT`
* `FACE_OF_CONIC`
* `POLYHEDRON_CONVEX_CONE_HULL`
* `POLYTOPE_IMP_BOUNDED`
* `AFF_DIM_PSUBSET`
* `CONIC_CONTAINS_0`
* `EMPTY_INTERIOR_SUBSET_HYPERPLANE`
* `EULER_POLYHEDRAL_CONE`

### Porting notes
When porting this lemma to another proof assistant, special attention should be paid to the handling of:
* Polytopes and their faces
* Conic hulls and their properties
* Affine hulls and their properties
* The Euler

---

## EULER_POINCARE_SPECIAL

### Name of formal statement
EULER_POINCARE_SPECIAL

### Type of the formal statement
Theorem

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
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[]]])
```

### Informal statement
For all `p` which are polytopes in `real^N` where `N` has dimension at least 2 and the affine hull of `p` is the set of all points `x` such that `x$1 = 0`, it holds that the sum from `0` to `dimindex(:N) - 1` of `(-1)^d` times the cardinality of the set of faces `f` of `p` with affine dimension `d` equals `1`.

### Informal sketch
* The proof starts by assuming the premise that `p` is a polytope in `real^N` with `N` having dimension at least 2, and the affine hull of `p` is the hyperplane `x$1 = 0`.
* It then applies the `EULER_POINCARE_LEMMA` to the image of `p` under a specific translation, leveraging `POLYTOPE_TRANSLATION_EQ` and `AFFINE_HULL_TRANSLATION` to establish key equalities.
* The proof proceeds by rewriting and simplifying expressions involving faces of `p`, their dimensions, and the application of `SUM_EQ_NUMSEG` to handle the summation.
* Key steps involve showing injectivity and using properties of `CARD` to count faces, leveraging `FINITE_POLYTOPE_FACES` and `INJECTIVE_IMAGE`.
* The proof concludes by demonstrating that the sum over the alternating series of face counts equals `1`, as per the Euler-Poincaré formula.

### Mathematical insight
This theorem encodes a special case of the Euler-Poincaré formula, which relates the number of faces of a polytope in various dimensions to the Euler characteristic of the polytope. The formula is fundamental in algebraic topology and geometric combinatorics, providing insights into the structure of polytopes and their geometric and topological properties.

### Dependencies
#### Theorems
- `EULER_POINCARE_LEMMA`
- `SURJECTIVE_IMAGE_EQ`
- `SUM_EQ_NUMSEG`
- `CARD_IMAGE_INJ`
#### Definitions
- `polytope`
- `affine hull`
- `face_of`
- `aff_dim`
#### Other
- `FINITE_POLYTOPE_FACES`
- `INJECTIVE_IMAGE`

---

## EULER_POINCARE_FULL

### Name of formal statement
EULER_POINCARE_FULL

### Type of the formal statement
Theorem

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
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
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
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[]])
```

### Informal statement
For all `p` of type `real^N->bool`, if `p` is a polytope and the affine dimension of `p` equals the dimension index of `N`, then the sum from `0` to the dimension index of `N` of `(-1)^d` times the cardinality of the set of faces `f` of `p` such that the affine dimension of `f` equals `d` is equal to `1`.

### Informal sketch
* The proof starts by assuming `p` is a polytope and its affine dimension is equal to the dimension index of `N`.
* It defines a function `f` from `real^N` to `real^(N,1)finite_sum` and its image `s`.
* The proof uses `EULER_POINCARE_SPECIAL` on `s` and then applies various rewriting and simplification steps.
* It proves the linearity of `f` and uses this to establish properties about the image `s`.
* The proof involves showing that the sum of certain terms equals `1`, using properties of faces and dimensions.
* Key steps involve:
  + Establishing the linearity of `f` and its implications for `s`.
  + Using `FACES_OF_LINEAR_IMAGE` to relate faces of `p` to faces of `s`.
  + Applying `CARD_IMAGE_INJ` to show the cardinality of certain sets.
* The proof concludes by combining these results to show the desired sum equals `1`.

### Mathematical insight
This theorem is an instance of the Euler-Poincaré formula for polytopes, which relates the number of faces of various dimensions of a polytope to its topological properties. The formula is a fundamental result in combinatorial geometry and topology, and its proof involves understanding the structure of polytopes, their faces, and the effects of linear transformations.

### Dependencies
* `EULER_POINCARE_SPECIAL`
* `POLYTOPE_LINEAR_IMAGE`
* `AFFINE_HULL_LINEAR_IMAGE`
* `FACES_OF_LINEAR_IMAGE`
* `CARD_IMAGE_INJ`
* `FINITE_POLYTOPE_FACES`
* `INJECTIVE_IMAGE` 

### Porting notes
When porting this theorem to another proof assistant, pay special attention to:
* The representation of polytopes and their faces.
* The definition and properties of the `f` function and its image `s`.
* The use of `EULER_POINCARE_SPECIAL` and how it is applied to `s`.
* The proof's reliance on properties of linear transformations and their effects on faces and dimensions.
* Potential differences in handling binders, quantifiers, and summations between HOL Light and the target proof assistant.

---

## EULER_RELATION

### Name of formal statement
EULER_RELATION

### Type of the formal statement
Theorem

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
For all `p` of type `real^3->bool`, if `p` is a polytope and the affine dimension of `p` is 3, then the sum of the number of vertices of `p` (i.e., faces of `p` with affine dimension 0) and the number of faces of `p` with affine dimension 2, minus the number of edges of `p` (i.e., faces of `p` with affine dimension 1), equals 2.

### Informal sketch
* The proof starts by assuming `p` is a polytope in 3D space (`polytope p /\ aff_dim p = &3`).
* It then applies the `EULER_POINCARE_FULL` theorem to `p`, which provides a relationship between the numbers of faces of different dimensions.
* The proof involves rewriting and simplifying expressions using various tactics (`REWRITE_TAC`, `CONV_TAC`, `SIMP_TAC`) to manipulate the equation derived from `EULER_POINCARE_FULL`.
* Key steps involve recognizing that the set of faces of `p` with affine dimension 3 is just `{p}` itself, using `FACE_OF_REFL` and `POLYTOPE_IMP_CONVEX`.
* The proof concludes by algebraically simplifying the resulting equation to show that the Euler relation holds for `p`.

### Mathematical insight
This theorem expresses the Euler-Poincaré formula for polytopes in 3-dimensional space, which is a fundamental relationship in geometry and topology. The formula relates the numbers of vertices, edges, and faces of a polytope, providing a topological invariant. The theorem is important because it applies to all polytopes in 3D, offering a universal principle for their structure.

### Dependencies
#### Theorems
* `EULER_POINCARE_FULL`
* `FACE_OF_AFF_DIM_LT`
#### Definitions
* `polytope`
* `aff_dim`
* `face_of`
#### Other
* `DIMINDEX_3`
* `TOP_DEPTH_CONV`
* `SUM_CLAUSES_NUMSEG`
* `REAL_MUL_LID`
* `REAL_MUL_LNEG`
* `NOT_IN_EMPTY`
* `FINITE_EMPTY`
* `CARD_CLAUSES`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how polytopes and their faces are represented, as well as the specific formulation of the Euler-Poincaré formula. Differences in handling affine dimensions, face relationships, and possibly the arithmetic of cardinalities may require careful adaptation. Additionally, the use of `REPEAT STRIP_TAC` and other tactics may need to be translated into equivalent strategies in the target system, considering its specific proof automation and rewriting mechanisms.

---

