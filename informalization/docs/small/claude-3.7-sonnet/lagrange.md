# lagrange.ml

## Overview

Number of statements: 4

This file formalizes basic group theory concepts specifically to prove Lagrange's theorem, which states that the order of a subgroup divides the order of the parent group. It develops minimal definitions and results sufficient for this theorem, rather than providing a comprehensive treatment of group theory. The file operates independently of other libraries and contains a self-contained development, though users seeking a more extensive group theory formalization are directed to the separate `Library/grouptheory.ml` file.

## group

### group

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let group = new_definition
  `group(g,( ** ),i,(e:A)) <=>
    (e IN g) /\ (!x. x IN g ==> i(x) IN g) /\
    (!x y. x IN g /\ y IN g ==> (x ** y) IN g) /\
    (!x y z. x IN g /\ y IN g /\ z IN g ==> (x ** (y ** z) = (x ** y) ** z)) /\
    (!x. x IN g ==> (x ** e = x) /\ (e ** x = x)) /\
    (!x. x IN g ==> (x ** i(x) = e) /\ (i(x) ** x = e))`;;
```

### Informal statement
A 4-tuple $(g, *, i, e)$ is a group if and only if the following conditions hold:
1. The identity element $e$ belongs to the set $g$: $e \in g$
2. For all $x \in g$, the inverse function $i(x)$ is also in $g$: $\forall x. x \in g \Rightarrow i(x) \in g$
3. For all $x, y \in g$, the product $x * y$ is also in $g$: $\forall x, y. x \in g \land y \in g \Rightarrow (x * y) \in g$
4. The operation $*$ is associative: $\forall x, y, z \in g. (x * (y * z)) = ((x * y) * z)$
5. The element $e$ is the identity: $\forall x \in g. (x * e = x) \land (e * x = x)$
6. The function $i$ gives inverses: $\forall x \in g. (x * i(x) = e) \land (i(x) * x = e)$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This is the standard mathematical definition of a group, formulated as a 4-tuple $(g, *, i, e)$ where:
- $g$ is the carrier set containing all elements of the group
- $*$ is the binary operation (group multiplication)
- $i$ is the inverse function that maps each element to its inverse
- $e$ is the identity element

The definition encapsulates the core axioms of group theory:
- Closure under the operation (axiom 3)
- Associativity of the operation (axiom 4)
- Existence of an identity element (axiom 5)
- Existence of inverses for each element (axiom 6)

This formulation allows for abstract reasoning about groups without specifying the nature of the elements or operations. In HOL Light, the type parameter `A` is used to make the definition polymorphic, allowing it to be used with various types of group elements.

### Dependencies
#### Definitions
- `group` (self-referential)

### Porting notes
When porting this definition to other proof assistants:
1. Note that HOL Light uses a 4-tuple representation instead of a record type which some systems might prefer
2. Some systems might prefer defining groups with separate carrier set and operation components rather than as a tuple
3. In systems with dependent types (like Coq or Lean), you might want to use a dependent record type with the carrier set as a field and operations defined over that set
4. The definition assumes the existence of a notion of belonging (`IN`) which may be represented differently in different systems

---

## subgroup

### Name of formal statement
subgroup

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let subgroup = new_definition
  `subgroup h (g,( ** ),i,(e:A)) <=> h SUBSET g /\ group(h,( ** ),i,e)`;;
```

### Informal statement
A set $h$ is a subgroup of a group $(g, \ast, i, e)$ if and only if $h \subseteq g$ and $(h, \ast, i, e)$ is itself a group.

Formally, $\text{subgroup } h (g, \ast, i, e) \iff h \subseteq g \land \text{group}(h, \ast, i, e)$.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
The definition captures the standard mathematical notion of a subgroup in group theory. A subgroup is a subset of a group that is itself a group under the same operations. 

The key points of this definition are:
1. A subgroup must be a subset of the parent group.
2. The subgroup must itself satisfy all the group axioms using the same binary operation ($\ast$), identity element ($e$), and inverse function ($i$).

This definition is minimal but complete - it implicitly ensures that the subgroup contains the identity element, is closed under the group operation, and contains all inverses, since these properties are required by the `group` definition.

### Dependencies
#### Definitions
- `group`: Defines when a tuple $(g, \ast, i, e)$ forms a group, requiring the identity element $e$ to be in $g$, closure under the inverse function $i$ and binary operation $\ast$, associativity of $\ast$, identity properties of $e$, and inverse properties.

### Porting notes
When porting this definition to other proof assistants:
1. Ensure that the group definition is ported first.
2. Note that HOL Light uses a 4-tuple representation for groups, while some systems may use different representations (e.g., carrier set and operations as separate parameters).
3. The definition is straightforward and should translate directly to most systems with appropriate set theory and function notation.

---

## GROUP_LAGRANGE_COSETS

### GROUP_LAGRANGE_COSETS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let GROUP_LAGRANGE_COSETS = prove
 (`!g h ( ** ) i e.
        group (g,( ** ),i,e:A) /\ subgroup h (g,( ** ),i,e) /\ FINITE g
        ==> ?q. (CARD(g) = CARD(q) * CARD(h)) /\
                (!b. b IN g ==> ?a x. a IN q /\ x IN h /\ (b = a ** x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group; subgroup; SUBSET] THEN STRIP_TAC THEN
  ABBREV_TAC
   `coset = \a:A. {b:A | b IN g /\ (?x:A. x IN h /\ (b = a ** x))}` THEN
  SUBGOAL_THEN `!a:A. a IN g ==> a IN (coset a)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "coset" THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(h:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. FINITE((coset:A->A->bool) a)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "coset" THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `g:A->bool` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:A x:A y. a IN g /\ x IN g /\ y IN g /\ ((a ** x) :A = a ** y)
                ==> (x = y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(e:A ** x:A):A = e ** y` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN
     `((i(a):A ** a:A) ** x) = (i(a) ** a) ** y`
     (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:A. a IN g ==> (CARD(coset a :A->bool) = CARD(h:A->bool))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(coset:A->A->bool) (a:A) = IMAGE (\x. a ** x) (h:A->bool)`
    SUBST1_TAC THENL
     [EXPAND_TAC "coset" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A y. x IN g /\ y IN g ==> (i(x ** y) = i(y) ** i(x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(x:A ** y:A) :A` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(x:A ** (y ** i(y))) ** i(x)` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN g ==> (i(i(x)) = x)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(i:A->A)(x)` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a IN g /\ b IN g
          ==> ((coset:A->A->bool) a = coset b) \/
              ((coset a) INTER (coset b) = {})`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `((i:A->A)(b) ** a:A) IN (h:A->bool)` THENL
     [DISJ1_TAC THEN EXPAND_TAC "coset" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      GEN_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN
       `!x:A. x IN h ==> (b ** (i(b) ** a:A) ** x = a ** x) /\
                         (a ** i(i(b) ** a) ** x = b ** x)`
       (fun th -> EQ_TAC THEN REPEAT STRIP_TAC THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[th]) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISJ2_TAC THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN EXPAND_TAC "coset" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[TAUT `(a /\ b) /\ (a /\ c) <=> a /\ b /\ c`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(i(b:A) ** a ** y):A = i(b) ** b ** z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(i(b:A) ** a:A ** y):A = e ** z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(i(b:A) ** a:A ** y):A = z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((i(b:A) ** a:A) ** y):A = z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((i(b:A) ** a:A) ** y) ** i(y) = z ** i(y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(i(b:A) ** a:A) ** (y ** i(y)) = z ** i(y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(i(b:A) ** a:A) ** e = z ** i(y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(i(b:A) ** a:A):A = z ** i(y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{c:A | ?a:A. a IN g /\ (c = (@)(coset a))}` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> b /\ a`) THEN CONJ_TAC THENL
   [X_GEN_TAC `b:A` THEN DISCH_TAC THEN
    EXISTS_TAC `(@)((coset:A->A->bool) b)` THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `b:A` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(@)((coset:A->A->bool) b) IN (coset b)` MP_TAC THENL
     [REWRITE_TAC[IN] THEN MATCH_MP_TAC SELECT_AX THEN
      ASM_MESON_TAC[IN];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RATOR_CONV)
                         [SYM th]) THEN
    REWRITE_TAC[] THEN
    ABBREV_TAC `C = (@)((coset:A->A->bool) b)` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(i:A->A)(c)` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q = {c:A | ?a:A. a IN g /\ (c = (@)(coset a))}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!a:A b. a IN g /\ b IN g /\ a IN coset(b) ==> b IN coset(a)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "coset" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `(i:A->A) c` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:A b c. a IN coset(b) /\ b IN coset(c) /\ c IN g ==> a IN coset(c)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "coset" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:A b:A. a IN coset(b) ==> a IN g` ASSUME_TAC THENL
   [EXPAND_TAC "coset" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:A b. a IN coset(b) /\ b IN g ==> (coset a = coset b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN
    MAP_EVERY UNDISCH_TAC
     [`!a:A b:A. a IN coset(b) ==> a IN g`;
      `!a:A b c. a IN coset(b) /\ b IN coset(c) /\ c IN g ==> a IN coset(c)`;
      `!a:A b. a IN g /\ b IN g /\ a IN coset(b) ==> b IN coset(a)`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:A. a IN g ==> (@)(coset a):A IN (coset a)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `!a:A. a IN g ==> a IN coset a` THEN
    DISCH_THEN(MP_TAC o SPEC `a:A`) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN; SELECT_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:A. a IN q ==> a IN g` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:A x:A a' x'. a IN q /\ a' IN q /\ x IN h /\ x' IN h /\
                    ((a' ** x') :A = a ** x) ==> (a' = a) /\ (x' = x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `(c ==> a /\ b ==> d) ==> a /\ b /\ c ==> d`) THEN
    STRIP_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `a1:A` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `a2:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `a:A IN g /\ a' IN g` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `((coset:A->A->bool) a1 = coset a) /\ (coset a2 = coset a')`
    MP_TAC THENL
     [CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    ONCE_ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "coset" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `(x:A ** (i:A->A)(x')):A` THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `(a':A ** x':A):A = a ** x` THEN
    DISCH_THEN(MP_TAC o C AP_THM `(i:A->A) x'` o AP_TERM `(**):A->A->A`) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `g = IMAGE (\(a:A,x:A). (a ** x):A) {(a,x) | a IN q /\ x IN h}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN
    REWRITE_TAC[CONJ_ASSOC; ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD {(a:A,x:A) | a IN q /\ x IN h}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[PAIR_EQ] THEN REPEAT GEN_TAC THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_PRODUCT THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `g:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_PRODUCT THEN CONJ_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `g:A->bool` THEN
  ASM_REWRITE_TAC[SUBSET]);;
```

### Informal statement
For any group $(g, *, i, e)$ where $g$ is a finite set, if $h$ is a subgroup of $(g, *, i, e)$, then there exists a set $q$ such that:
1. $|g| = |q| \cdot |h|$ (the cardinality of the group equals the product of the cardinalities of $q$ and $h$)
2. For any element $b \in g$, there exist elements $a \in q$ and $x \in h$ such that $b = a * x$

In other words, the theorem states that the order of a finite group is divisible by the order of any of its subgroups, and that the group can be partitioned into cosets of the subgroup.

### Informal proof
The proof establishes that a finite group can be partitioned into cosets of a subgroup, and that all cosets have the same cardinality as the subgroup. The main steps are:

- Define the right coset of an element $a \in g$ as $\text{coset}(a) = \{b \in g \mid \exists x \in h, b = a * x\}$
- Show that any element $a \in g$ belongs to its own coset
- Prove that $h$ is finite (since it's a subset of the finite set $g$)
- Establish that all cosets are finite
- Prove a cancellation property: for $a, x, y \in g$, if $a * x = a * y$ then $x = y$
- Show that all cosets have the same cardinality as $h$ by establishing a bijection between $h$ and $\text{coset}(a)$ via the map $x \mapsto a * x$
- Prove that for any two elements of $g$, their cosets are either equal or disjoint by analyzing when $\text{coset}(a) = \text{coset}(b)$ or $\text{coset}(a) \cap \text{coset}(b) = \emptyset$
- Define $q$ as a set of representatives of the cosets: $q = \{c \mid \exists a \in g, c = \text{select}(\text{coset}(a))\}$ where $\text{select}$ picks an arbitrary element from each coset
- Show that every $b \in g$ can be expressed as $b = a * x$ where $a \in q$ and $x \in h$
- Establish that this representation is unique: if $a * x = a' * x'$ with $a, a' \in q$ and $x, x' \in h$, then $a = a'$ and $x = x'$
- Demonstrate that $g$ can be written as the image of the Cartesian product of $q$ and $h$ under the group operation
- Conclude that $|g| = |q| \cdot |h|$ using properties of cardinality of images and products

### Mathematical insight
Lagrange's theorem is one of the most fundamental results in group theory. This particular formulation explicitly constructs the set of coset representatives $q$ and proves the divisibility relation between the orders of the group and its subgroup.

The proof demonstrates that a group can be partitioned into disjoint cosets of a subgroup, all having equal cardinality. This result has many important consequences:

1. It establishes the concept of the index of a subgroup as the number of cosets
2. It forms the basis for Lagrange's theorem, which states that the order of a subgroup divides the order of the finite group
3. It introduces the concept of quotient structures in group theory

The proof technique using cosets and a set of representatives is standard in abstract algebra and shows how the structure of a group can be decomposed with respect to a subgroup.

### Dependencies
- Group theoretical concepts:
  - `group`: Definition of a group as a 4-tuple $(g, *, i, e)$ where $g$ is the underlying set, $*$ is the binary operation, $i$ is the inverse function, and $e$ is the identity element
  - `subgroup`: Definition of a subgroup as a subset of a group that forms a group under the same operations

- Set theory and cardinality theorems:
  - `FINITE_SUBSET`: A subset of a finite set is finite
  - `CARD_IMAGE_INJ`: Cardinality preservation under injective functions
  - `CARD_PRODUCT`: Cardinality of a Cartesian product equals the product of cardinalities
  - `FINITE_PRODUCT`: Finiteness of the Cartesian product of finite sets

### Porting notes
When porting this theorem:
1. Ensure the ported system has appropriate definitions of groups, subgroups, and cosets
2. The proof relies heavily on set-theoretic operations and cardinality properties, which should be available in most proof assistants
3. In systems with dependent types, the group operation type might need explicit adjustment
4. The use of the selection operator (`@`) to pick representatives from cosets may require different approaches in other systems:
   - In constructive systems, you might need to use choice principles or explicit selection functions
   - Alternatively, you could define $q$ as the set of minimal elements from each coset under some well-ordering

---

## GROUP_LAGRANGE

### GROUP_LAGRANGE
- GROUP_LAGRANGE

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let GROUP_LAGRANGE = prove
 (`!g h ( ** ) i e.
        group (g,( ** ),i,e:A) /\ subgroup h (g,( ** ),i,e) /\ FINITE g
        ==> (CARD h) divides (CARD g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP GROUP_LAGRANGE_COSETS) THEN
  MESON_TAC[DIVIDES_LMUL; DIVIDES_REFL]);;
```

### Informal statement
For any group $(g, **, i, e)$ with carrier set $g$, binary operation $**$, inverse function $i$, and identity element $e$ of type $A$, if $h$ is a subgroup of $(g, **, i, e)$ and $g$ is finite, then the cardinality of $h$ divides the cardinality of $g$.

Formally:
$$\forall g, h, **, i, e: \text{group}(g, **, i, e) \wedge \text{subgroup}(h, g, **, i, e) \wedge \text{FINITE}(g) \Rightarrow \text{CARD}(h) \text{ divides } \text{CARD}(g)$$

### Informal proof
The proof uses Lagrange's theorem for cosets (GROUP_LAGRANGE_COSETS), which establishes that for a finite group $g$ with subgroup $h$, there exists a set $q$ such that:
1. $\text{CARD}(g) = \text{CARD}(q) \cdot \text{CARD}(h)$
2. For all $b \in g$, there exist $a \in q$ and $x \in h$ such that $b = a ** x$

From this result, we directly conclude that $\text{CARD}(h)$ divides $\text{CARD}(g)$ using basic properties of divisibility:
- $\text{DIVIDES}_\text{LMUL}$: if $d$ divides $a$, then $d$ divides $(x \cdot a)$
- $\text{DIVIDES}_\text{REFL}$: every number divides itself

Since $\text{CARD}(g) = \text{CARD}(q) \cdot \text{CARD}(h)$, and by $\text{DIVIDES}_\text{REFL}$ we know $\text{CARD}(h)$ divides itself, we can apply $\text{DIVIDES}_\text{LMUL}$ to conclude $\text{CARD}(h)$ divides $\text{CARD}(g)$.

### Mathematical insight
This theorem is the famous Lagrange's theorem in group theory, one of the most fundamental results in the field. It establishes that the order (cardinality) of any subgroup must divide the order of the parent group.

The key insight is that the cosets of a subgroup partition the group into equally-sized equivalence classes. This partitioning is what creates the divisibility relationship between the sizes of the subgroup and the whole group.

Lagrange's theorem has many important applications in group theory, including:
- Constraining possible sizes of subgroups
- The basis for Fermat's Little Theorem and Euler's Theorem in number theory
- The foundation for the concept of the index of a subgroup

### Dependencies
- Theorems:
  - `DIVIDES_REFL`: For any number $x$, $x$ divides $x$
  - `DIVIDES_LMUL`: For all $d$, $a$, and $x$, if $d$ divides $a$, then $d$ divides $(x \cdot a)$
  - `GROUP_LAGRANGE_COSETS`: The coset decomposition theorem that shows $\text{CARD}(g) = \text{CARD}(q) \cdot \text{CARD}(h)$
- Definitions:
  - `divides`: $a$ divides $b$ if there exists $x$ such that $b = a \cdot x$
  - `group`: Definition of a group with carrier set, operation, inverse, and identity
  - `subgroup`: Definition of a subgroup as a subset that is itself a group

### Porting notes
When porting this theorem:
1. Ensure your system has a suitable encoding of finite groups and subgroups
2. Some proof assistants may have built-in algebraic libraries that already contain Lagrange's theorem
3. Depending on the system, you might need to handle the subset relationship between the subgroup and group explicitly
4. The proof is simple once the more complex GROUP_LAGRANGE_COSETS result is established

---

