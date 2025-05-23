# derangements.ml

## Overview

Number of statements: 43

The `derangements.ml` file formalizes the concept of derangements, specifically focusing on a formula for the number of derangements given by `round[n!/e]`. It builds upon imports from `transc.ml`, `calc_real.ml`, and `floor.ml` to establish this mathematical concept. The file's content is centered around defining and proving properties related to derangements, contributing to the library's collection of mathematical theories. Its purpose is to provide a formal foundation for reasoning about derangements within the HOL Light system.

## domain

### Name of formal statement
domain

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let domain = new_definition
 `domain r = {x | ?y. r(x,y)};;
```

### Informal statement
The domain of a relation `r` is defined as the set of all `x` such that there exists a `y` where `r(x, y)` holds.

### Informal sketch
* The definition of `domain` involves a set comprehension that ranges over all `x` for which there exists at least one `y` satisfying the relation `r(x, y)`.
* This step mirrors the mathematical notion of a domain in relational mathematics, where the domain of a relation is the set of all elements that appear as the first component of an ordered pair in the relation.
* The key logical stage here is the application of existential quantification (`?y`) to assert the existence of at least one `y` for each `x` in the domain.

### Mathematical insight
The `domain` definition is fundamental in relational algebra and set theory, as it allows for the identification of the set of elements that are related to at least one other element under a given relation `r`. This concept is crucial for understanding and working with relations in various mathematical and computational contexts.

### Dependencies
* `new_definition`
* Set comprehension and existential quantification (`?y`)

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles set comprehensions and existential quantification. For example, in Lean, you might use the `∃` symbol for existential quantification and set comprehension syntax to define the domain of a relation. In Coq, you could use the `exists` keyword and set notation to achieve a similar definition. Ensure that the target system's libraries for set theory and relations are properly utilized to align with the original HOL Light definition.

---

## range

### Name of formal statement
range

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let range = new_definition
 `range r = {y | ?x. r(x,y)};;
```

### Informal statement
The `range` of a relation `r` is defined as the set of all `y` such that there exists an `x` for which `r(x, y)` holds.

### Informal sketch
* The definition of `range` involves a set comprehension, which constructs a set by describing its elements.
* The set comprehension uses an existential quantifier `?x` to assert the existence of an `x` for each `y` in the resulting set.
* The relation `r(x, y)` is used as the criterion for including `y` in the set.
* This definition can be understood as collecting all the "images" or "targets" of the relation `r`.

### Mathematical insight
The `range` definition is fundamental in describing the behavior of relations, capturing the idea of where a relation "points to". It's essential in various areas of mathematics, such as set theory, category theory, and relational algebra, providing a way to discuss the "output" or "codomain" of a relation in a precise manner.

### Dependencies
* `new_definition`
* Relations and set theory basics, such as set comprehension and existential quantification.

### Porting notes
When translating this definition into another proof assistant, pay attention to how set comprehension and existential quantification are handled. Some systems may use different notations or have built-in support for relations and their properties. For example, in Lean, you might use the `∃` symbol for existential quantification and `{x | P x}` for set comprehension, while in Coq, you could use `exists` and `fun x => P x` within a `sig` type or a set defined using `Collect`.

---

## id

### Name of formal statement
id

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let id = new_definition
 `id(s) (x,y) <=> x IN s /\ x = y`;;
```

### Informal statement
The `id` relation on a set `s` holds for pairs `(x, y)` if and only if `x` is an element of `s` and `x` is equal to `y`.

### Informal sketch
* The definition of `id` involves a straightforward assertion about set membership and equality.
* It does not require a complex proof or construction, as it is a basic definition.
* The key logical stage is the conjunction of `x IN s` and `x = y`, which must both hold for `id(s) (x, y)` to be true.

### Mathematical insight
The `id` relation represents the identity relation on a set, where each element is related only to itself. This is a fundamental concept in mathematics, particularly in relation algebra and category theory, as it provides a baseline for comparing and composing relations.

### Dependencies
#### Definitions
* `IN` (set membership)
* `=` (equality)

---
### Name of formal statement
compose

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let compose = new_definition
 `(r % s) (x,y) <=> ?z. r(x,z) /\ s(z,y)`;;
```

### Informal statement
The composition of relations `r` and `s`, denoted `r % s`, holds for pairs `(x, y)` if and only if there exists a `z` such that `r(x, z)` and `s(z, y)`.

### Informal sketch
* The definition of `compose` involves existential quantification to find an intermediate element `z`.
* The key logical stages are:
  * Establishing the existence of `z`
  * Verifying `r(x, z)` and `s(z, y)` for that `z`
* This composition is a fundamental operation in relational algebra, allowing the combination of relations to form new ones.

### Mathematical insight
The composition of relations is crucial in many areas of mathematics and computer science, such as database query languages, formal language theory, and category theory. It allows for the creation of complex relations from simpler ones, enabling the modeling of various structures and processes.

### Dependencies
#### Definitions
* `r` and `s` (relations)
#### Inference Rules
* Existential quantification (`?z`)

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles relational composition and existential quantification. Some systems may have built-in support for relational algebra, while others may require manual definition or the use of specific libraries. Additionally, the syntax for existential quantification and the composition operator may vary.

---

## converse

### Name of formal statement
converse

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let converse = new_definition `converse(r) (x,y) = r(y,x)`
```

### Informal statement
The converse of a relation `r` is defined as a relation that holds between `x` and `y` if and only if `r` holds between `y` and `x`.

### Informal sketch
* The definition introduces a new relation `converse(r)` that takes a relation `r` as input.
* The `converse(r)` relation is defined as a binary relation on pairs `(x, y)`, where `(x, y)` is in `converse(r)` if and only if `(y, x)` is in `r`.
* This definition essentially reverses the direction of the relation `r`.

### Mathematical insight
The converse relation is a fundamental concept in mathematics, allowing us to reverse the direction of a given relation. This is useful in various areas, such as graph theory, where it can be used to reverse the direction of edges, or in logic, where it can be used to dualize statements.

### Dependencies
* None

### Porting notes
When porting this definition to other proof assistants, note that the concept of a converse relation is likely to be already defined or easily definable. In Lean, for example, this could be defined using a simple function `converse : (α → α → Prop) → (α → α → Prop)` that takes a relation `r` and returns its converse. In Coq, a similar definition could be made using a function `converse : relation A → relation A`.

---

## swap

### Name of formal statement
swap

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let swap = new_definition
 `swap(a,b) (x,y) <=> x = a /\ y = b \/ x = b /\ y = a`;;
```

### Informal statement
The `swap` function takes two arguments `a` and `b` and applies to an ordered pair `(x, y)`, such that `swap(a, b)(x, y)` holds if and only if either `x` equals `a` and `y` equals `b`, or `x` equals `b` and `y` equals `a`.

### Informal sketch
* The definition involves a logical equivalence (`<=>`) that characterizes the `swap` function.
* It applies to pairs `(x, y)` and checks two conditions:
  + Whether `x` is equal to `a` and `y` is equal to `b`.
  + Whether `x` is equal to `b` and `y` is equal to `a`.
* The `swap` function essentially describes a transposition operation, flipping the positions of `a` and `b` in the pair `(x, y)`.

### Mathematical insight
The `swap` function represents a simple yet fundamental concept of transposing elements within a pair, which is crucial in various mathematical structures, particularly in combinatorics, algebra, and logic. It formalizes the idea of exchanging two elements, which is a basic operation in many mathematical contexts.

### Dependencies
* None explicitly mentioned, but relies on basic logical and equality principles, such as `/\` (conjunction), `\/` (disjunction), and `=` (equality).

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles function definitions, especially those involving logical equivalences and pair structures. Note that the syntax for defining functions and logical operators may differ significantly between HOL Light and the target system. Additionally, consider how the target system treats equality and how it is applied to pairs or other data structures.

---

## REL_TAC

### Name of formal statement
REL_TAC

### Type of the formal statement
Tactic definition

### Formal Content
```ocaml
let REL_TAC =
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; EXISTS_PAIR_THM; PAIR_BETA_THM;
              permutes; pairsup; domain; range; compose; id; converse; swap;
              deranges; IN_INSERT; IN_DELETE; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  REWRITE_TAC[IN; EMPTY; INSERT; DELETE; UNION; IN_ELIM_THM; PAIR_EQ;
              id; converse; swap] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  ASM_MESON_TAC[]
```

### Informal statement
The `REL_TAC` tactic is defined as a sequence of operations to simplify and solve goals involving relations. It starts by applying `ALL_TAC` to all assumptions, then applies a series of rewrites using various theorems and definitions related to relations, such as `FUN_EQ_THM`, `FORALL_PAIR_THM`, `EXISTS_PAIR_THM`, `PAIR_BETA_THM`, `permutes`, `pairsup`, `domain`, `range`, `compose`, `id`, `converse`, `swap`, `deranges`, `IN_INSERT`, `IN_DELETE`, `NOT_IN_EMPTY`, and `IN_ELIM_THM`. It then applies additional rewrites and simplifications using `STRIP_TAC`, `EQ_TAC`, and substitution tactics to ultimately apply `ASM_MESON_TAC` to solve the goal.

### Informal sketch
* The tactic begins with applying `ALL_TAC` to all assumptions, setting up the context for further simplifications.
* It then applies a series of rewrites using theorems and definitions related to relations, aiming to simplify the goal by applying properties of relations such as `permutes`, `pairsup`, and `deranges`.
* The tactic uses `REPEAT` to iteratively apply `STRIP_TAC` or `EQ_TAC` to simplify the goal further, potentially revealing opportunities for substitution.
* Substitution tactics are applied to replace variables in the conclusion with terms from the assumptions, using both `SUBST_ALL_TAC` and its symmetric version.
* Finally, `ASM_MESON_TAC` is applied to solve the goal, leveraging the simplified form and substitutions made in the previous steps.

### Mathematical insight
The `REL_TAC` tactic is designed to automate the process of working with relations in a formal proof system. By applying a series of rewrites and simplifications, it aims to leverage the properties of relations, such as bijectivity and permutations, to solve goals. This tactic is important for streamlining proofs involving complex relational structures, making it easier to reason about these concepts in a formal setting.

### Dependencies
#### Theorems and definitions
* `FUN_EQ_THM`
* `FORALL_PAIR_THM`
* `EXISTS_PAIR_THM`
* `PAIR_BETA_THM`
* `permutes`
* `pairsup`
* `domain`
* `range`
* `compose`
* `id`
* `converse`
* `swap`
* `deranges`
* `IN_INSERT`
* `IN_DELETE`
* `NOT_IN_EMPTY`
* `IN_ELIM_THM`
* `IN`
* `EMPTY`
* `INSERT`
* `DELETE`
* `UNION`
* `PAIR_EQ`

### Porting notes
When translating `REL_TAC` into another proof assistant, pay close attention to how relations and their properties are handled. Differences in how binders, substitutions, and rewrites are implemented may require adjustments to the tactic's sequence of operations. Specifically, ensure that the target system supports similar `REPEAT` and `REWRITE_TAC` mechanisms, and that the theorems and definitions used are appropriately translated or re-proven in the new context.

---

## REL_RULE

### Name of formal statement
REL_RULE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let REL_RULE tm = prove(tm,REL_TAC);;
```

### Informal statement
The `REL_RULE` theorem states that for a given term `tm`, it proves `tm` using the `REL_TAC` tactic.

### Informal sketch
* The proof involves applying the `REL_TAC` tactic to the term `tm`.
* The `REL_TAC` tactic is used to prove the term `tm` by relational reasoning.
* The main logical stage is the application of `REL_TAC` to `tm`, which involves using relational properties to derive the proof.

### Mathematical insight
The `REL_RULE` theorem provides a way to prove terms using relational reasoning, which is a fundamental concept in formal methods. This theorem is important because it allows for the use of relational properties to derive proofs, which can be useful in a variety of applications.

### Dependencies
* `REL_TAC`
* `prove`

### Porting notes
When porting this theorem to other proof assistants, note that the equivalent of `REL_TAC` may need to be defined or imported. Additionally, the `prove` function may need to be replaced with the equivalent proof construction mechanism in the target proof assistant.

---

## CONVERSE_COMPOSE

### Name of formal statement
CONVERSE_COMPOSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CONVERSE_COMPOSE = prove
 (`!r s. converse(r % s) = converse(s) % converse(r)`,
  REL_TAC)
```

### Informal statement
For all relations `r` and `s`, the converse of the composition of `r` and `s` is equal to the composition of the converse of `s` and the converse of `r`.

### Informal sketch
* The proof involves establishing a property of relation composition and converse.
* The `REL_TAC` tactic in HOL Light suggests that the proof is carried out using relational properties and tactics.
* To mirror this in another proof assistant, one would:
  + Define the composition of relations `r` and `s` as `r % s`.
  + Define the converse of a relation `r` as `converse(r)`.
  + Use relational properties to prove the equality `converse(r % s) = converse(s) % converse(r)` for all relations `r` and `s`.
* Key steps involve understanding how the converse operation distributes over relation composition and leveraging existing relational properties.

### Mathematical insight
This theorem provides insight into how the converse operation interacts with relation composition, which is fundamental in the study of relations and their properties. Understanding how these operations interact is crucial for more complex constructions and proofs involving relations.

### Dependencies
* `converse`
* `REL_TAC`

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles relational properties and the converse operation. Specifically:
* Ensure that the definition of relation composition and converse aligns with the target system's libraries or definitions.
* Identify the appropriate tactics or automation in the target system that correspond to `REL_TAC` in HOL Light.
* Be mindful of any differences in how binders or quantifiers are handled between HOL Light and the target system, as this may affect the proof strategy.

---

## CONVERSE_CONVERSE

### Name of formal statement
CONVERSE_CONVERSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CONVERSE_CONVERSE = prove
 (`!r. converse(converse r) = r`,
  REL_TAC)
```

### Informal statement
For all relations `r`, the converse of the converse of `r` is equal to `r`.

### Informal sketch
* The proof involves showing that the converse operation is idempotent when applied twice to any relation `r`.
* The `REL_TAC` tactic in HOL Light suggests that the proof relies on basic properties of relations and perhaps the definition of the converse operation.
* Key steps likely include:
  + Applying the definition of `converse` to `converse r` to find `converse (converse r)`.
  + Using properties of relations to simplify and show that this equals the original relation `r`.

### Mathematical insight
This theorem is important because it shows that taking the converse of a relation twice returns the original relation, which is a fundamental property in the theory of relations. It indicates a kind of symmetry or stability under the converse operation, which is crucial in various mathematical and logical contexts.

### Dependencies
* `converse`
* Basic properties of relations

### Porting notes
When translating this theorem into another proof assistant, pay attention to how relations and their converses are defined and handled. The proof may require direct application of relation properties or may involve more abstract tactics depending on the target system's libraries and automation capabilities. Specifically, ensure that the converse operation and its properties are defined or imported correctly, and that the system's tactics for relations are used appropriately to mirror the `REL_TAC` approach in HOL Light.

---

## PAIRSUP_EXPLICIT

### Name of formal statement
PAIRSUP_EXPLICIT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PAIRSUP_EXPLICIT = prove
 (`!p s t.
        p pairsup (s,t) <=>
        (!x y. p(x,y) ==> x IN s /\ y IN t) /\
        (!x. x IN s ==> ?!y. y IN t /\ p(x,y)) /\
        (!y. y IN t ==> ?!x. x IN s /\ p(x,y))`,
  REL_TAC)
```

### Informal statement
For all relations `p`, sets `s`, and sets `t`, the relation `p` pairs up `s` and `t` if and only if for all `x` and `y`, whenever `p(x,y)` holds, `x` is an element of `s` and `y` is an element of `t`, and for every `x` in `s`, there exists a unique `y` in `t` such that `p(x,y)` holds, and for every `y` in `t`, there exists a unique `x` in `s` such that `p(x,y)` holds.

### Informal sketch
* The theorem `PAIRSUP_EXPLICIT` establishes an equivalence between the relation `p` pairing up sets `s` and `t` and three conditions:
 + The first condition ensures that whenever `p(x,y)` holds, `x` is in `s` and `y` is in `t`.
 + The second condition requires that for each `x` in `s`, there exists a unique `y` in `t` such that `p(x,y)` holds, which is achieved using the `?!` (unique existence) quantifier.
 + The third condition is symmetric to the second, requiring that for each `y` in `t`, there exists a unique `x` in `s` such that `p(x,y)` holds.
* The proof uses `REL_TAC`, indicating a tactic for relational properties, to establish this equivalence.

### Mathematical insight
The `PAIRSUP_EXPLICIT` theorem provides a detailed characterization of what it means for a relation to pair up two sets. This is important in various areas of mathematics, such as graph theory, combinatorics, and category theory, where relations between sets are fundamental. The theorem's conditions ensure a bijective correspondence between the elements of the two sets via the relation, which is crucial for many mathematical constructions and proofs.

### Dependencies
* `pairsup`
* `REL_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles relational properties and quantifiers, especially the unique existence quantifier `?!`. The tactic `REL_TAC` might not have a direct counterpart, so understanding its purpose in establishing relational equivalences will be key to finding an appropriate strategy in the target system.

---

## PERMUTES_EXPLICIT

### Name of formal statement
PERMUTES_EXPLICIT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERMUTES_EXPLICIT = prove
 (`!p s. p permutes s <=>
         (!x y. p(x,y) ==> x IN s /\ y IN s) /\
         (!x. x IN s ==> ?!y. y IN s /\ p(x,y)) /\
         (!y. y IN s ==> ?!x. x IN s /\ p(x,y))`,
  REL_TAC)
```

### Informal statement
For all relations `p` and sets `s`, `p` permutes `s` if and only if three conditions hold: 
1. For all `x` and `y`, if `p(x, y)` then both `x` is in `s` and `y` is in `s`.
2. For all `x` in `s`, there exists a unique `y` in `s` such that `p(x, y)`.
3. For all `y` in `s`, there exists a unique `x` in `s` such that `p(x, y)`.

### Informal sketch
* The proof involves establishing the equivalence between `p` permuting `s` and the three given conditions.
* The `REL_TAC` tactic in HOL Light is used for relational reasoning, which involves manipulating relations and their properties.
* Key steps include:
  + Showing that if `p` permutes `s`, then the conditions are met, which involves using the definition of permutation and the properties of relations.
  + Showing the converse, that if the conditions are met, then `p` permutes `s`, which may involve constructing a permutation from the given conditions.

### Mathematical insight
This statement formalizes the concept of a permutation of a set in terms of a relation. A permutation of a set `s` is a bijective function from `s` to itself, which can also be viewed as a relation `p` where for every `x` in `s`, there is exactly one `y` in `s` such that `p(x, y)`, and vice versa. This theorem provides an explicit characterization of when a relation represents a permutation of a set.

### Dependencies
* `permutes`
* Basic properties of relations and sets, including the definition of a relation permuting a set.

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system represents relations and sets, as well as how they handle quantifiers and relational properties. Specifically, the use of `REL_TAC` in HOL Light may need to be replaced with tactics or constructs specific to the target system that are capable of handling relational reasoning. Additionally, the definition of permutation and the properties of relations may need to be explicitly stated or imported from relevant libraries in the target system.

---

## PAIRSUP_DOMRAN

### Name of formal statement
PAIRSUP_DOMRAN

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PAIRSUP_DOMRAN = prove
 (`!p s t. p pairsup (s,t) ==> domain p = s /\ range p = t`,
  REL_TAC)
```

### Informal statement
For all relations `p`, sets `s`, and sets `t`, if `p` is the sup of the pair `(s, t)`, then the domain of `p` is equal to `s` and the range of `p` is equal to `t`.

### Informal sketch
* The proof involves assuming `p pairsup (s, t)` and then using this assumption to derive `domain p = s` and `range p = t`.
* The `REL_TAC` tactic in HOL Light is used to handle relation properties, indicating that the proof may involve manipulating relation properties to establish the equalities.
* Key steps likely involve using the definition of `pairsup` to relate `p` with the pair `(s, t)`, and then applying properties of relations, such as the definition of domain and range, to establish the desired equalities.

### Mathematical insight
This theorem provides a fundamental property about the relationship between a relation `p` that is the supremum of a pair of sets `(s, t)` and the domain and range of `p`. It essentially characterizes how `p` is determined by `s` and `t` in terms of its domain and range, which is crucial for understanding and working with relations in the context of set theory and relation algebra.

### Dependencies
* `pairsup`
* `domain`
* `range`
* Possibly: `REL_TAC` (though this is a tactic rather than a formal item like a theorem or definition)

### Porting notes
When translating this into another proof assistant, special attention should be paid to how relations and their properties (like domain and range) are handled. The concept of `pairsup` and its relation to the domain and range might need to be defined or proven in the target system if it does not have direct equivalents. Additionally, the automation provided by `REL_TAC` in HOL Light may need to be replicated using tactics or automation available in the target proof assistant.

---

## PERMUTES_DOMRAN

### Name of formal statement
PERMUTES_DOMRAN

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERMUTES_DOMRAN = prove
 (`!p s. p permutes s ==> domain p = s /\ range p = s`,
  REL_TAC)
```

### Informal statement
For all permutations `p` and sets `s`, if `p` permutes `s`, then the domain of `p` is equal to `s` and the range of `p` is equal to `s`.

### Informal sketch
* The proof starts with the assumption that `p` permutes `s`, which implies that `p` is a bijection from `s` to `s`.
* The `REL_TAC` tactic is used to reason about the relational properties of `p` and derive the equality of the domain and range of `p` with `s`.
* The key logical stage involves recognizing that a permutation `p` of `s` must have `s` as both its domain and range, due to the definition of a permutation.

### Mathematical insight
This theorem is important because it formalizes a fundamental property of permutations: they are bijections that map a set onto itself. Understanding this property is crucial in various areas of mathematics, such as group theory and combinatorics, where permutations play a central role.

### Dependencies
* `permutes`
* `domain`
* `range`
* `REL_TAC`

### Porting notes
When porting this theorem to another proof assistant, pay attention to how permutations and their properties are defined and handled. Specifically, ensure that the target system's `permutes` definition aligns with the one used in HOL Light, and that the relational tactics or their equivalents are available for deriving the domain and range equalities.

---

## PAIRSUP_FUNCTIONAL

### Name of formal statement
PAIRSUP_FUNCTIONAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PAIRSUP_FUNCTIONAL = prove
 (`!p s t. p pairsup (s,t) ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y'`,
  REL_TAC)
```

### Informal statement
For all predicates `p` and for all `s` and `t`, if `p` is related to the pair `(s, t)` by the `pairsup` relation, then for all `x`, `y`, and `y'`, if `p(x, y)` and `p(x, y')`, then `y` equals `y'`.

### Informal sketch
* The proof starts with the assumption that `p` is related to `(s, t)` by `pairsup`.
* It then considers arbitrary `x`, `y`, and `y'` and assumes that both `p(x, y)` and `p(x, y')` hold.
* Using the `REL_TAC` tactic, it aims to derive `y = y'`, leveraging the properties of the `pairsup` relation and the given predicate `p`.
* The key insight is to apply relational properties to constrain the possible values of `y` and `y'` given `p(x, y)` and `p(x, y')`, leading to the conclusion that `y` must equal `y'`.

### Mathematical insight
This theorem captures the functional property of a relation `p` when it is related to a pair `(s, t)` via `pairsup`. Essentially, it states that if `p` behaves like a function (in the sense that for each `x`, there is at most one `y` such that `p(x, y)`), then for any `x`, `y`, and `y'` where `p(x, y)` and `p(x, y')`, it must be the case that `y = y'`. This is crucial in establishing that `p` acts as a function, which is a fundamental concept in mathematics and computer science.

### Dependencies
* `pairsup`
* `REL_TAC`

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles relational properties and predicate logic. The `REL_TAC` tactic in HOL Light is used for relational reasoning, so equivalent tactics or strategies in the target system should be identified. Additionally, ensure that the target system's representation of `pairsup` and its properties aligns with the original HOL Light formulation to maintain the theorem's validity.

---

## PERMUTES_FUNCTIONAL

### Name of formal statement
PERMUTES_FUNCTIONAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERMUTES_FUNCTIONAL = prove
 (`!p s. p permutes s ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y'`,
  REL_TAC)
```

### Informal statement
For all permutations `p` of a set `s`, if `p` maps `x` to `y` and `p` also maps `x` to `y'`, then `y` is equal to `y'`.

### Informal sketch
* The theorem starts with a universal quantification over a permutation `p` of a set `s`.
* It then assumes that `p` is a permutation of `s`, which implies that `p` is a bijective function.
* The next step involves another universal quantification over elements `x`, `y`, and `y'` of `s`.
* Given that `p(x, y)` and `p(x, y')`, the theorem concludes that `y` equals `y'`, leveraging the injective property of `p`.
* The proof uses the `REL_TAC` tactic, indicating a relation-based approach to establish the functional behavior of the permutation.

### Mathematical insight
This theorem captures the functional property of a permutation, which is a crucial aspect of set theory and combinatorics. It ensures that a permutation, being a bijective mapping, assigns each element in the domain to exactly one element in the codomain, thereby acting as a function.

### Dependencies
* `permutes`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how each system handles permutations and functional properties. Specifically, ensure that the target system's definition of a permutation implies bijectivity, which is essential for this theorem. Additionally, the use of `REL_TAC` in HOL Light may correspond to different tactics or built-in mechanisms for handling relational properties in other systems.

---

## PAIRSUP_COFUNCTIONAL

### Name of formal statement
PAIRSUP_COFUNCTIONAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PAIRSUP_COFUNCTIONAL = prove
 (`!p s t. p pairsup (s,t) ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x'`,
  REL_TAC)
```

### Informal statement
For all predicates `p` and all `s` and `t`, if `p` is a pair-sup of `(s, t)`, then for all `x`, `x'`, and `y`, if `p(x, y)` and `p(x', y)`, then `x` equals `x'`.

### Informal sketch
* The proof starts with the assumption that `p` is a pair-sup of `(s, t)`, which implies certain properties about `p`.
* The goal is to show that for any `x`, `x'`, and `y`, if `p(x, y)` and `p(x', y)`, then `x = x'`.
* The `REL_TAC` tactic in HOL Light is used to handle the relational properties, which likely involves using the definition of `pairsup` and properties of equality.

### Mathematical insight
This theorem captures a fundamental property of functions, specifically that a function cannot map two different inputs to the same output. The `pairsup` relation likely encodes a condition that ensures `p` behaves functionally. Understanding this theorem requires recognizing the interplay between the `pairsup` relation, the predicate `p`, and the implications of functional behavior.

### Dependencies
* `pairsup`
* `REL_TAC`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how functions and relations are defined and used. The concept of `pairsup` might need to be defined or imported from a library, and the relational properties might be handled differently. For example, in Lean, you might use `rel` or `funext` tactics to handle similar relational goals, while in Coq, you could use `relation` or `functional_extensionality`. In Isabelle, `relation` and `fun_eq_iff` might be relevant. Ensure that the translation preserves the original's logical structure and quantifier scope.

---

## PERMUTES_COFUNCTIONAL

### Name of formal statement
PERMUTES_COFUNCTIONAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERMUTES_COFUNCTIONAL = prove
 (`!p s. p permutes s ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x'`,
  REL_TAC)
```

### Informal statement
For all functions `p` and sets `s`, if `p` permutes `s`, then for all `x`, `x'`, and `y`, if `p(x, y)` and `p(x', y)`, then `x` equals `x'`.

### Informal sketch
* The proof assumes `p` permutes `s`, which implies that `p` is a bijection on `s`.
* It then considers arbitrary `x`, `x'`, and `y` such that `p(x, y)` and `p(x', y)`.
* The goal is to show that `x = x'` under these conditions, leveraging the fact that `p` is a function and thus has unique outputs for given inputs.
* The `REL_TAC` tactic suggests the use of relational properties of functions to establish the uniqueness of `x` given `y`.

### Mathematical insight
This theorem captures a fundamental property of functions that permute a set: for any given output `y`, there is at most one input `x` that maps to `y` under the permutation, due to the injective nature of permutations. This is crucial in establishing the bijective nature of permutations and has implications in various areas of mathematics where permutations are used.

### Dependencies
* `permutes`
* Basic properties of functions and relations, including injectivity and the definition of a permutation.

### Porting notes
When translating this theorem into other proof assistants, pay attention to how each system represents permutations and functions. Specifically, ensure that the permutation property is correctly defined and that the proof steps logically follow from the properties of functions and relations. Note that `REL_TAC` is a HOL Light tactic, so the corresponding proof in another system would involve relational reasoning but might not have a direct tactical equivalent.

---

## PAIRSUP_ID

### Name of formal statement
PAIRSUP_ID

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PAIRSUP_ID = prove
 (`!s. id(s) pairsup (s,s)`,
  REL_TAC)
```

### Informal statement
For all sets `s`, the identity relation `id(s)` is a superset of the pair `(s, s)`.

### Informal sketch
* The theorem `PAIRSUP_ID` asserts a property about the relationship between the identity relation `id(s)` and the pair `(s, s)` for any set `s`.
* The proof involves using the `REL_TAC` tactic, which suggests that it relies on relational properties.
* The key logical stage is recognizing that the identity relation `id(s)` by definition includes all pairs of the form `(s, s)`, thus it is a superset of the set containing just `(s, s)`.

### Mathematical insight
This theorem is important because it establishes a basic property about the identity relation in relation to set pairs. It's a foundational result that could be used in various contexts where identity relations and their properties are crucial, such as in equivalence relations, group theory, or category theory.

### Dependencies
#### Theorems
* `id`
* `pairsup`
#### Definitions
* `id`
* `pairsup`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system represents relations and set operations. Specifically, the `REL_TAC` tactic in HOL Light is used for relational properties, so the equivalent tactic or method in the target system should be used. Additionally, ensure that the representation of the identity relation and the notion of a superset are correctly translated, as these may differ slightly between systems.

---

## PERMUTES_ID

### Name of formal statement
PERMUTES_ID

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERMUTES_ID = prove
 (`!s. id(s) permutes s`,
  REL_TAC)
```

### Informal statement
For all sets `s`, the identity function `id(s)` permutes `s`.

### Informal sketch
* The theorem `PERMUTES_ID` asserts that the identity function `id` permutes any set `s`.
* The proof involves showing that `id(s)` satisfies the definition of a permutation, which typically involves demonstrating that `id(s)` is both injective and surjective.
* The `REL_TAC` tactic in HOL Light is used to prove the statement, which likely involves applying basic properties of equality and set membership.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the identity function in relation to permutations. It provides a basis for more complex arguments about permutations and functions, demonstrating that the identity function preserves the structure of any set.

### Dependencies
#### Theorems and definitions
* `id`
* `permutes`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how each system represents the identity function and permutations. Ensure that the definition of `permutes` and the properties of `id` are correctly aligned with the target system's libraries and theorems. Additionally, the automation and tactic mechanisms may differ, so the `REL_TAC` tactic might need to be replaced with equivalent constructs in the target proof assistant.

---

## PAIRSUP_CONVERSE

### Name of formal statement
PAIRSUP_CONVERSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_CONVERSE = prove
 (`!p s t. p pairsup (s,t) ==> converse(p) pairsup (t,s)`,
  REL_TAC)
```

### Informal statement
For all relations `p` and all pairs `(s, t)`, if `p` is a pair-supremum of `(s, t)`, then the converse of `p` is a pair-supremum of `(t, s)`.

### Informal sketch
* The proof starts by assuming `p pairsup (s, t)`, which means `p` is a pair-supremum of `(s, t)`.
* The goal is to show that `converse(p)` is a pair-supremum of `(t, s)`.
* The `REL_TAC` tactic is used to reason about the relation `p` and its converse.

### Mathematical insight
This theorem establishes a relationship between the pair-supremum of a relation and the pair-supremum of its converse. It provides a way to dualize results about pair-suprema, which is useful in various mathematical contexts, such as lattice theory and order theory.

### Dependencies
* `pairsup`
* `converse`

### Porting notes
When porting this theorem to another proof assistant, note that the `REL_TAC` tactic may not have a direct equivalent. The proof may require manual reasoning about the relation `p` and its converse, using the properties of pair-suprema and converse relations. Additionally, the representation of relations and their converses may differ between proof assistants, requiring adjustments to the proof script.

---

## PERMUTES_CONVERSE

### Name of formal statement
PERMUTES_CONVERSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERMUTES_CONVERSE = prove
 (`!p s. p permutes s ==> converse(p) permutes s`,
  REL_TAC)
```

### Informal statement
For all permutations `p` and sets `s`, if `p` permutes `s`, then the converse of `p` also permutes `s`.

### Informal sketch
* The proof starts with the assumption that `p` permutes `s`, which means that `p` is a bijection from `s` to itself.
* The goal is to show that `converse(p)` also permutes `s`, i.e., it is a bijection from `s` to itself.
* The proof likely involves showing that `converse(p)` is both injective and surjective, using the properties of `p` and the definition of converse.
* The `REL_TAC` tactic suggests that the proof involves relational properties and tactics.

### Mathematical insight
This theorem is important because it shows that the property of permuting a set is preserved under taking the converse of a permutation. This is a fundamental property of permutations and is used in various areas of mathematics, such as group theory and combinatorics.

### Dependencies
* `permutes`
* `converse`

### Porting notes
When porting this theorem to another proof assistant, note that the `REL_TAC` tactic may not have a direct equivalent. The proof may need to be reconstructed using the specific tactics and libraries available in the target system. Additionally, the definition of `permutes` and `converse` may need to be ported or redefined in the target system.

---

## PAIRSUP_COMPOSE

### Name of formal statement
PAIRSUP_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_COMPOSE = prove
 (`!p p' s t u. p pairsup (s,t) /\ p' pairsup (t,u) ==> (p % p') pairsup (s,u)`,
  REL_TAC)
```

### Informal statement
For all relations `p`, `p'`, and all elements `s`, `t`, `u`, if `p` is a pair supervisor of `(s, t)` and `p'` is a pair supervisor of `(t, u)`, then the composition of `p` and `p'` is a pair supervisor of `(s, u)`.

### Informal sketch
* The proof starts by assuming `p pairsup (s, t)` and `p' pairsup (t, u)`, which implies that `p` and `p'` are relations that supervise the pairs `(s, t)` and `(t, u)` respectively.
* The goal is to show that the composition `p % p'` supervises the pair `(s, u)`.
* The proof uses relational properties and the definition of `pairsup` to establish the desired result.
* The `REL_TAC` tactic in HOL Light is used to apply relational properties and tactics to prove the theorem.

### Mathematical insight
This theorem provides a way to compose pair supervisors, which is essential in constructing and reasoning about complex relations in a modular and hierarchical manner. The ability to compose supervisors enables the creation of more sophisticated relational structures, which can be used to model and analyze various systems and phenomena.

### Dependencies
* `pairsup`
* `%` (relation composition)

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of relational composition and the definition of `pairsup`. The `REL_TAC` tactic in HOL Light may not have a direct equivalent in other systems, so the proof may need to be reconstructed using the target system's relational reasoning mechanisms. Additionally, the representation of relations and their properties may differ between systems, requiring careful translation of the theorem's statement and proof.

---

## PERMUTES_COMPOSE

### Name of formal statement
PERMUTES_COMPOSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERMUTES_COMPOSE = prove
 (`!p p' s. p permutes s /\ p' permutes s ==> (p % p') permutes s`,
  REL_TAC)
```

### Informal statement
For all permutations `p`, `p'`, and sets `s`, if `p` permutes `s` and `p'` permutes `s`, then the composition of `p` and `p'` (denoted as `p % p'`) also permutes `s`.

### Informal sketch
* The proof starts with the assumption that `p` and `p'` are permutations of `s`.
* It then applies the definition of permutation to `p` and `p'`, which implies that both `p` and `p'` are bijections on `s`.
* The composition `p % p'` is then considered, and it is shown that this composition also satisfies the properties of a permutation on `s`.
* The `REL_TAC` tactic is used to establish the relational properties required for the composition to be a permutation.

### Mathematical insight
This theorem is important because it shows that the composition of two permutations is also a permutation, which is a fundamental property in group theory and combinatorics. It implies that the set of permutations of a set forms a group under composition.

### Dependencies
* `permutes`
* `REL_TAC`

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of permutations and relational properties. The `REL_TAC` tactic in HOL Light is used for establishing relational properties, which might need to be replaced with equivalent tactics or strategies in the target system. Additionally, the definition and properties of permutations might need to be adapted or re-proven in the context of the target proof assistant.

---

## PERMUTES_SWAP

### Name of formal statement
PERMUTES_SWAP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERMUTES_SWAP = prove (`swap(a,b) permutes {a,b}`, REL_TAC);;
```

### Informal statement
The theorem `PERMUTES_SWAP` states that the function `swap(a,b)` is a permutation of the set `{a,b}`, meaning it rearranges the elements of the set in a way that every element in the original set appears exactly once in the resulting arrangement.

### Informal sketch
* The proof involves showing that `swap(a,b)` satisfies the properties of a permutation, specifically that it is a bijection (one-to-one and onto) between the set `{a,b}` and itself.
* The `REL_TAC` tactic is used to reason about the relational properties of the `swap` function, likely involving the use of `swap`'s definition to establish the bijective nature of the mapping.
* Key steps may involve:
  + Showing that `swap(a,b)` is injective (one-to-one), i.e., `swap(a,b) x = swap(a,b) y` implies `x = y` for all `x` and `y` in `{a,b}`.
  + Showing that `swap(a,b)` is surjective (onto), i.e., for every `z` in `{a,b}`, there exists an `x` in `{a,b}` such that `swap(a,b) x = z`.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the `swap` function, which is commonly used in combinatorial and algebraic structures. The fact that `swap(a,b)` is a permutation of `{a,b}` has implications for the study of symmetric groups and the representation of permutations in mathematics.

### Dependencies
* `swap`
* `permutes`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system represents permutations and bijections. Specifically, consider how to express the `swap` function and the `permutes` property in the target system, and how to adapt the `REL_TAC` tactic or its equivalent to reason about these relational properties.

---

## PAIRSUP_EMPTY

### Name of formal statement
PAIRSUP_EMPTY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PAIRSUP_EMPTY = prove
 (`p pairsup ({},{}) <=> (p = {})`,
  REL_TAC)
```

### Informal statement
The theorem `PAIRSUP_EMPTY` states that a predicate `p` is pairwise supremum over the empty set and the empty set if and only if `p` is equal to the empty set.

### Informal sketch
* The proof involves showing the equivalence between `p pairsup ({},{})` and `p = {}`.
* The `REL_TAC` tactic is used to prove this equivalence, which likely involves using properties of relations and possibly substitution or rewriting.
* Key steps may involve:
  + Showing that if `p` is the pairwise supremum over the empty sets, then `p` must be empty, as there are no elements to consider.
  + Proving the converse, that if `p` is empty, then it satisfies the condition for being the pairwise supremum over the empty sets, as this condition is vacuously true.

### Mathematical insight
The `PAIRSUP_EMPTY` theorem provides a foundational result about the pairwise supremum operation, specifically when applied to the most basic case involving empty sets. It highlights the degenerate case where the only possible pairwise supremum over two empty sets is the empty set itself, underlining the consistency and boundary conditions of the pairwise supremum operation.

### Dependencies
* `pairsup`
* `REL_TAC`

### Porting notes
When translating `PAIRSUP_EMPTY` into another proof assistant, ensure that the representation of the empty set and the pairwise supremum operation (`pairsup`) is correctly defined and understood. Note that the `REL_TAC` tactic may not have a direct equivalent, so the proof strategy might need to be adapted based on the target system's capabilities for handling relational properties and equivalences.

---

## PAIRSUP_INSERT

### Name of formal statement
PAIRSUP_INSERT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PAIRSUP_INSERT = prove
 (`!x:A s t:B->bool p.
        p pairsup (x INSERT s,t) <=>
          if x IN s then p pairsup (s,t)
          else ?y q. y IN t /\ p = (x,y) INSERT q /\ q pairsup (s,t DELETE y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SET_RULE `x IN s ==> x INSERT s = s`] THEN EQ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `?y. y IN t /\ p(x:A,y:B)` MP_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  EXISTS_TAC `p DELETE (x:A,y:B)` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REL_TAC)
```

### Informal statement
For all `x` of type `A`, sets `s` and `t` of type `B -> bool`, and `p`, the following holds: `p` is a superset of the pair `(x INSERT s, t)` if and only if either `x` is in `s` and `p` is a superset of `(s, t)`, or there exists a `y` in `t` such that `p` equals `(x, y) INSERT q` and `q` is a superset of `(s, t DELETE y)`.

### Informal sketch
* The proof starts by considering the case when `x` is in `s`, using `COND_CASES_TAC` to split the condition.
* If `x` is in `s`, then `x INSERT s` equals `s` by the `SET_RULE`, and the proof simplifies using `ASM_SIMP_TAC`.
* For the case when `x` is not in `s`, the proof searches for a `y` in `t` such that `p(x, y)` holds, utilizing `SUBGOAL_THEN` and `MP_TAC`.
* It then uses `MATCH_MP_TAC MONO_EXISTS` to introduce an existential quantifier for `y` and applies `X_GEN_TAC` to generalize over `y`.
* The proof constructs a `q` such that `p` equals `(x, y) INSERT q` and shows `q` is a superset of `(s, t DELETE y)` using `EXISTS_TAC` and `REL_TAC`.
* Key HOL Light terms involved include `PAIRSUP`, `INSERT`, `DELETE`, and `SUBGOAL_THEN`.

### Mathematical insight
This theorem provides insight into the relationship between a superset `p` of a pair of sets `(s, t)` and the insertion of an element `x` into `s`. It essentially states that `p` being a superset of `(x INSERT s, t)` can be broken down into two cases: either `x` is already in `s`, in which case the condition simplifies to `p` being a superset of `(s, t)`, or there exists a `y` in `t` such that `p` can be expressed in terms of `x`, `y`, and another set `q` that is a superset of `(s, t DELETE y)`. This theorem is crucial for reasoning about set operations and supersets in the context of pairs of sets.

### Dependencies
* **Theorems:**
  + `SET_RULE`
  + `MONO_EXISTS`
* **Definitions:**
  + `PAIRSUP`
  + `INSERT`
  + `DELETE`

---

## NUMBER_OF_PAIRINGS

### Name of formal statement
NUMBER_OF_PAIRINGS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NUMBER_OF_PAIRINGS = prove
(`!n s:A->bool t:B->bool.
        s HAS_SIZE n /\ t HAS_SIZE n
        ==> {p | p pairsup (s,t)} HAS_SIZE (FACT n)`,
  let lemma = prove
   (`{p | ?y. y IN t /\ A y p} = UNIONS {{p | A y p} | y IN t} /\
     {p | ?q. p = (a,y) INSERT q /\ A y q} =
           IMAGE (\q. (a,y) INSERT q) {q | A y q}`,
    CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS; IN_IMAGE] THEN SET_TAC[]) in
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[HAS_SIZE_CLAUSES] THEN
    SIMP_TAC[PAIRSUP_EMPTY; SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH; FACT];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [HAS_SIZE_CLAUSES] THEN
  REWRITE_TAC[HAS_SIZE_SUC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[PAIRSUP_INSERT; RIGHT_EXISTS_AND_THM; lemma; FACT] THEN
  MATCH_MP_TAC HAS_SIZE_UNIONS THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE_SUC];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_SIMP_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC])
```

### Informal statement
For all natural numbers `n` and sets `s` and `t` with `n` elements, if `s` and `t` both have `n` elements, then the set of all pairings `p` that pair up elements from `s` and `t` has a size equal to the factorial of `n`.

### Informal sketch
* The proof starts by considering the base case where `s` and `t` are empty, and then proceeds by induction on the size `n` of `s` and `t`.
* In the inductive step, it uses a `lemma` to establish properties about the set of pairings and how it relates to inserting elements into pairings.
* The `INDUCT_TAC` and `REPEAT GEN_TAC` tactics are used to set up the inductive proof and handle the general case.
* The `GEN_REWRITE_TAC` and `REWRITE_TAC` tactics are applied to simplify expressions involving `HAS_SIZE`, `PAIRSUP`, and other set operations.
* The `MATCH_MP_TAC` tactic is used to apply the `HAS_SIZE_UNIONS` theorem, which is crucial for establishing the size of the set of pairings.
* Key steps involve recognizing the disjointness of certain sets and applying the `HAS_SIZE_IMAGE_INJ` theorem to conclude the size of the image of a set under a certain function.

### Mathematical insight
This theorem provides a fundamental result about the number of ways to pair up elements from two sets of the same size, which is essential in combinatorics and permutations. The proof illustrates how inductive reasoning and careful manipulation of set operations can be used to establish a deep result about the size of a complex set.

### Dependencies
* Theorems:
  + `HAS_SIZE_UNIONS`
  + `HAS_SIZE_IMAGE_INJ`
  + `PAIRSUP_INSERT`
  + `RIGHT_EXISTS_AND_THM`
* Definitions:
  + `HAS_SIZE`
  + `PAIRSUP`
  + `FACT`
* Inductive rules:
  + `INDUCT_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles inductive proofs, set operations, and the representation of functions like `FACT`. Note that the `lemma` proved within the main proof may need to be established separately or integrated differently, depending on the target system's support for nested proofs. Additionally, the use of tactics like `GEN_REWRITE_TAC` and `MATCH_MP_TAC` may require equivalent tactical machinery in the target system to apply theorems and simplify expressions effectively.

---

## NUMBER_OF_PERMUTATIONS

### Name of formal statement
NUMBER_OF_PERMUTATIONS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NUMBER_OF_PERMUTATIONS = prove
 (`!s n. s HAS_SIZE n ==> {p | p permutes s} HAS_SIZE (FACT n)`,
  SIMP_TAC[permutes; NUMBER_OF_PAIRINGS]);;
```

### Informal statement
For all sets `s` and natural numbers `n`, if `s` has `n` elements, then the set of all permutations `p` of `s` has a size equal to the factorial of `n`.

### Informal sketch
* The proof involves establishing a relationship between the size of a set `s` and the number of permutations of its elements.
* It utilizes the `permutes` concept to define what constitutes a permutation of `s`.
* The `SIMP_TAC` tactic is applied with `permutes` and `NUMBER_OF_PAIRINGS` to simplify the statement and potentially derive the conclusion about the size of the set of permutations being the factorial of the set's size.
* Key to the proof is understanding how `permutes` and `NUMBER_OF_PAIRINGS` (or `FACT`) relate to the combinatorial concept of permutations and how these are formalized in HOL Light.

### Mathematical insight
This theorem formalizes a fundamental combinatorial principle: the number of ways to arrange `n` distinct items is `n!` (n factorial), which is a cornerstone of counting and permutations in mathematics. The theorem's importance lies in its application to any set of distinct elements, providing a basis for further reasoning about permutations in various mathematical contexts.

### Dependencies
- `permutes`
- `NUMBER_OF_PAIRINGS` (or `FACT`)

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how permutations are defined and how the concept of the size of a set is handled. Additionally, ensure that the target system has an equivalent to the `SIMP_TAC` tactic or can achieve similar simplifications through other means. The factorial function and its properties may also need to be defined or imported from a library, depending on the target system's standard library.

---

## derangements

### Name of formal statement
derangements

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let derangements = define
`(derangements 0 = 1) /\
  (derangements 1 = 0) /\
  (derangements(n + 2) = (n + 1) * (derangements n + derangements(n + 1)))`;;
```

### Informal statement
The `derangements` function is defined by three clauses: 
- `derangements 0` equals 1, 
- `derangements 1` equals 0, and 
- for any natural number `n`, `derangements (n + 2)` equals `(n + 1)` times the sum of `derangements n` and `derangements (n + 1)`.

### Informal sketch
* The definition of `derangements` is given recursively, with base cases for `derangements 0` and `derangements 1`.
* For `n >= 2`, the definition of `derangements (n + 2)` depends on the values of `derangements n` and `derangements (n + 1)`, indicating a recursive relationship.
* The key step in constructing this definition involves recognizing the pattern in derangements and encoding it in a recursive formula.

### Mathematical insight
The `derangements` function calculates the number of derangements of a set with `n` elements, which are permutations of the elements where no element appears in its original position. This definition is important in combinatorics and has applications in various fields, including probability theory and computer science.

### Dependencies
* No specific theorems or definitions are listed as dependencies, but the definition relies on basic arithmetic operations and recursive function definition principles.

### Porting notes
When translating this definition into another proof assistant, pay attention to how recursive functions are defined and how the specific arithmetic operations are handled. Some systems might require explicit type annotations or different syntax for recursive definitions. Additionally, consider how the proof assistant handles the commutativity and associativity of arithmetic operations, as these properties might be used implicitly in the HOL Light definition.

---

## DERANGEMENT_INDUCT

### Name of formal statement
DERANGEMENT_INDUCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DERANGEMENT_INDUCT = prove
 (`!P. P 0 /\ P 1 /\ (!n. P n /\ P(n + 1) ==> P(n + 2)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[ARITH])
```

### Informal statement
For all predicates P, if P holds for 0 and 1, and for all natural numbers n, if P holds for n and n+1, then P also holds for n+2, then P holds for all natural numbers n.

### Informal sketch
* The proof starts by assuming a predicate P and using `GEN_TAC` to generalize it.
* It then applies `STRIP_TAC` to remove the universal quantifier and `SUBGOAL_THEN` to create a subgoal for `!n. P n /\ P(n + 1)`, which is then proven using `MESON_TAC`.
* The proof proceeds with `INDUCT_TAC` to perform induction, and `ASM_SIMP_TAC` is applied with `ADD1` and `GSYM ADD_ASSOC` to simplify the arithmetic expressions.
* Further simplification is done using `ASM_SIMP_TAC` with `ARITH` to finalize the proof.

### Mathematical insight
This theorem is a form of strong induction, where the inductive step is strengthened by assuming the statement holds for two consecutive numbers instead of just one. This is useful for proving properties of sequences or functions where each term depends on the previous two terms.

### Dependencies
* `ADD1`
* `GSYM ADD_ASSOC`
* `ARITH`

### Porting notes
When translating this theorem into other proof assistants, note that the `INDUCT_TAC` and `ASM_SIMP_TAC` tactics may have different equivalents. For example, in Lean, `INDUCT_TAC` might be replaced with `induction`, and `ASM_SIMP_TAC` might be replaced with `simp`. Additionally, the `SUBGOAL_THEN` and `MESON_TAC` tactics may require manual intervention to recreate the subgoal and apply the appropriate tactics.

---

## DERANGEMENT_ADD2

### Name of formal statement
DERANGEMENT_ADD2

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DERANGEMENT_ADD2 = prove
 (`!p s x y.
        p deranges s /\ ~(x IN s) /\ ~(y IN s) /\ ~(x = y)
        ==> ((x,y) INSERT (y,x) INSERT p) deranges (x INSERT y INSERT s)`,
  REL_TAC)
```

### Informal statement
For all permutations `p`, sets `s`, and distinct elements `x` and `y` not in `s`, if `p` deranges `s` and `x` and `y` are not in `s` and are distinct, then the permutation obtained by inserting `(x, y)` and `(y, x)` into `p` deranges the set obtained by inserting `x` and `y` into `s`.

### Informal sketch
* Start with a permutation `p` that deranges a set `s`.
* Consider two elements `x` and `y` not in `s` and ensure they are distinct.
* Construct a new permutation by inserting the pairs `(x, y)` and `(y, x)` into `p`.
* Construct a new set by inserting `x` and `y` into `s`.
* The theorem states that this new permutation deranges the new set.
* The proof involves using relational properties, as indicated by the `REL_TAC` tactic in HOL Light, to establish the derangement property of the new permutation on the new set.

### Mathematical insight
This theorem provides a way to expand a derangement of a set by adding two new elements while maintaining the derangement property. It is essential in constructing or analyzing derangements of larger sets by iteratively adding elements and ensuring the derangement condition holds. The theorem relies on the properties of permutations and derangements, showcasing how to extend a derangement in a structured manner.

### Dependencies
* `deranges`
* Set theory basics (e.g., `IN`, `INSERT`)

### Porting notes
When translating this theorem into another proof assistant, pay attention to how permutations and derangements are represented. The concept of inserting pairs into a permutation and elements into a set should be translated carefully, considering the specific data structures and operations available in the target system. Additionally, the `REL_TAC` tactic suggests a relational approach to the proof, which might be handled differently in other proof assistants, potentially involving different automation or manual proof steps.

---

## DERANGEMENT_ADD1

### Name of formal statement
DERANGEMENT_ADD1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DERANGEMENT_ADD1 = prove
 (`!p s y x. p deranges s /\ ~(y IN s) /\ p(x,z)
             ==> ((x,y) INSERT (y,z) INSERT (p DELETE (x,z)))
                 deranges (y INSERT s)`,
  REL_TAC)
```

### Informal statement
For all permutations `p`, sets `s`, elements `y`, and `x`, if `p` deranges `s` and `y` is not in `s` and `p` maps `x` to some element `z`, then the permutation that maps `x` to `y`, `y` to `z`, and is otherwise like `p` except for mapping `x` to `z`, deranges the set `s` with `y` added to it.

### Informal sketch
* Start with the assumption that `p` deranges `s`, meaning no element in `s` is fixed by `p`.
* Consider an element `y` not in `s` and an element `x` in `s` such that `p(x) = z`.
* Construct a new permutation by mapping `x` to `y`, `y` to `z`, and otherwise following `p` except for the mapping of `x` to `z`, which is removed.
* The goal is to show this new permutation deranges `s` with `y` added to it.
* The proof involves showing that no element in `y INSERT s` is fixed by this new permutation, leveraging the fact that `p` deranges `s` and the specific adjustments made to `p`.

### Mathematical insight
This theorem provides insight into how derangements can be constructed or modified by adding elements to the set being deranged and adjusting the permutation accordingly. It's a step in understanding how derangements behave under certain operations, which is crucial in combinatorial and algebraic studies.

### Dependencies
* `deranges`
* `INSERT`
* `DELETE`
* Basic properties of permutations and set operations

### Porting notes
When translating this into other proof assistants, pay close attention to how each system handles permutations, set operations, and the `deranges` relation. The `REL_TAC` tactic in HOL Light is used for relational reasoning, which might be handled differently in other systems. Additionally, the representation of permutations and the `deranges` property may vary, requiring adjustments in the formal statement and its proof.

---

## DERANGEMENT_EMPTY

### Name of formal statement
DERANGEMENT_EMPTY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DERANGEMENT_EMPTY = prove
 (`!p. p deranges {} <=> p = {}`,
  REL_TAC)
```

### Informal statement
For all permutations `p`, `p` deranges the empty set if and only if `p` is equal to the empty set.

### Informal sketch
* The theorem `DERANGEMENT_EMPTY` establishes a relationship between a permutation `p` and its action on the empty set.
* The proof involves showing that a permutation `p` deranges the empty set (i.e., `p deranges {}`) is equivalent to `p` being the empty set itself (`p = {}`).
* The `REL_TAC` tactic suggests that the proof may involve relational properties or equivalence relations.

### Mathematical insight
This theorem provides insight into the properties of derangements, specifically how they interact with the empty set. A derangement is a permutation of the elements of a set, such that no element appears in its original position. In the context of the empty set, this theorem highlights a fundamental property: the only permutation that deranges the empty set is the empty permutation itself.

### Dependencies
* `deranges`

### Porting notes
When porting this theorem to another proof assistant, pay attention to how derangements and permutations are defined and how relational properties are handled. The `REL_TAC` tactic in HOL Light may correspond to different tactics or built-in mechanisms in other systems for establishing equivalence relations. Ensure that the target system's library includes definitions for derangements and permutations, and that these align with the mathematical structure expected by this theorem.

---

## DERANGEMENT_SING

### Name of formal statement
DERANGEMENT_SING

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DERANGEMENT_SING = prove
 (`!x p. ~(p deranges {x})`,
  REL_TAC)
```

### Informal statement
For all `x` and for all permutations `p`, it is not the case that `p` deranges the set containing only `x`.

### Informal sketch
* The proof involves showing that no permutation `p` can derange a singleton set `{x}`.
* The key insight is recognizing that a derangement must map every element to a different element, which is impossible for a set with only one element.
* The `REL_TAC` tactic in HOL Light is used to establish this result, leveraging relational properties of permutations.

### Mathematical insight
This statement is important because it highlights a fundamental property of derangements: they require at least two elements to exist. A derangement, by definition, is a permutation of the elements of a set, such that no element appears in its original position. For a set with only one element, there is no other position to map to, making derangement impossible.

### Dependencies
#### Theorems
* None explicitly mentioned, but the concept of `deranges` is crucial.
#### Definitions
* `deranges`

### Porting notes
When translating this theorem into another proof assistant, pay attention to how derangements and permutations are defined and handled. The key challenge will be ensuring that the notion of derangement is correctly captured, especially in how it applies to singleton sets. Additionally, the automation provided by `REL_TAC` in HOL Light might need to be manually replicated or matched with an equivalent tactic in the target system.

---

## NUMBER_OF_DERANGEMENTS

### Name of formal statement
NUMBER_OF_DERANGEMENTS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NUMBER_OF_DERANGEMENTS = prove
 (`!n s:A->bool. s HAS_SIZE n ==> {p | p deranges s} HAS_SIZE (derangements n)`,
  MATCH_MP_TAC DERANGEMENT_INDUCT THEN REWRITE_TAC[derangements] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `{}:A#A->bool` THEN
    ASM_REWRITE_TAC[DERANGEMENT_EMPTY; EXTENSION; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_SING] THEN MESON_TAC[MEMBER_NOT_EMPTY];
    CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[DERANGEMENT_SING] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN X_GEN_TAC `t:A->bool` THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = SUC(n + 1)`; HAS_SIZE_CLAUSES] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `{p | p deranges (x:A INSERT s)} =
        (IMAGE (\(y,p). (x,y) INSERT (y,x) INSERT p)
               {(y,p) | y IN s /\ p IN {p | p deranges (s DELETE y)}}) UNION
        (IMAGE (\(y,p). let z = @z. p(x,z) in
                        (x,y) INSERT (y,z) INSERT (p DELETE (x,z)))
               {(y,p) | y IN s /\
                        p IN {p | p deranges (x INSERT (s DELETE y))}})`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[TAUT `(a <=> b) <=> (b ==> a) /\ (a ==> b)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNION; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`;
                  FORALL_AND_THM; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[FORALL_PAIR_THM; PAIR_BETA_THM; IN_ELIM_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
      CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`y:A`; `p:A#A->bool`] THEN
      STRIP_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
         `y IN s ==> s = y INSERT (s DELETE y)`)) THEN
        MATCH_MP_TAC DERANGEMENT_ADD2 THEN ASM_REWRITE_TAC[IN_DELETE] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      ABBREV_TAC `z = @z. p(x:A,z:A)` THEN
      SUBGOAL_THEN `(p:A#A->bool)(x:A,z:A)` STRIP_ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
        CONV_TAC SELECT_CONV THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `z:A IN s` STRIP_ASSUME_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      SUBGOAL_THEN `(x:A) INSERT s = y INSERT (x INSERT (s DELETE y))`
      SUBST1_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC DERANGEMENT_ADD1 THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[IN_DELETE; IN_INSERT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `p:A#A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?y. y IN s /\ p(x:A,y:A)` STRIP_ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN ASM_CASES_TAC `(p:A#A->bool)(y,x)` THENL
     [DISJ1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `y:A,(p DELETE (y,x)) DELETE (x:A,y:A)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[PAIR_BETA_THM] THEN MAP_EVERY UNDISCH_TAC
         [`(p:A#A->bool)(x,y)`; `(p:A#A->bool)(y,x)`] THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `?z. p(y:A,z:A)` STRIP_ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `z:A IN s` ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_BETA_THM] THEN
    EXISTS_TAC `y:A` THEN
    EXISTS_TAC `(x:A,z:A) INSERT ((p DELETE (x,y)) DELETE (y,z))` THEN
    SUBGOAL_THEN
     `(@w:A. ((x,z) INSERT (p DELETE (x,y) DELETE (y,z))) (x,w)) = z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SELECT_UNIQUE THEN REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; PAIR_BETA_THM] THEN
      REWRITE_TAC[IN; INSERT; DELETE; PAIR_BETA_THM; IN_ELIM_THM; PAIR_EQ] THEN
      MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN
      ASM_CASES_TAC `u:A = x` THEN ASM_REWRITE_TAC[] THENL
       [ALL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN MATCH_MP_TAC HAS_SIZE_UNION THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
      REWRITE_TAC[FUN_EQ_THM; INSERT; IN_ELIM_THM; FORALL_PAIR_THM;
                  PAIR_EQ] THEN
      UNDISCH_TAC `~(x:A IN s)` THEN REL_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:A->bool) HAS_SIZE (n + 1)` THEN
    SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE] THEN
    ASM_REWRITE_TAC[ADD_SUB];

    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN MAP_EVERY X_GEN_TAC
       [`y:A`; `p:(A#A)->bool`; `y':A`; `p':(A#A->bool)`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      MAP_EVERY ABBREV_TAC [`z = @z. p(x:A,z:A)`; `z' = @z. p'(x:A,z:A)`] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      SUBGOAL_THEN `p(x:A,z:A) /\ p'(x:A,z':A)` STRIP_ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
        CONJ_TAC THEN CONV_TAC SELECT_CONV THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
        ALL_TAC] THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o SYM)) THEN
      SUBGOAL_THEN `z:A IN s /\ z':A IN s` STRIP_ASSUME_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
                           CONJ_TAC THEN MP_TAC th)
      THENL
       [DISCH_THEN(MP_TAC o C AP_THM `(x:A,y:A)`) THEN
        REWRITE_TAC[INSERT; DELETE; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b ==> a ==> c`] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_CASES_TAC `z':A = z` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC;
        DISCH_THEN(MP_TAC o C AP_THM `(y:A,z:A)`) THEN
        REWRITE_TAC[INSERT; DELETE; IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
        REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `a INSERT b INSERT s = a INSERT b INSERT t
        ==> ~(a IN s) /\ ~(a IN t) /\ ~(b IN s) /\ ~(b IN t) ==> s = t`)) THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(s:A->bool) HAS_SIZE n + 1` THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_DELETE] THEN
    ASM_SIMP_TAC[CARD_DELETE; CARD_CLAUSES; FINITE_DELETE] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN ARITH_TAC;

    REWRITE_TAC[DISJOINT] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_INTER; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `p:A#A->bool`] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_BETA_THM; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:A`; `q:A#A->bool`] THEN
    REWRITE_TAC[PAIR_BETA_THM; IN_ELIM_THM; PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `w = @w. q(x:A,w:A)` THEN
    SUBGOAL_THEN `(q:A#A->bool)(x:A,w:A)` STRIP_ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
      CONV_TAC SELECT_CONV THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `w:A IN s` STRIP_ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN FIRST_X_ASSUM(K ALL_TAC o SYM) THEN
    ASM_CASES_TAC `w:A = z` THEN ASM_REWRITE_TAC[] THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `w:A = y` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `y:A = z` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC; ALL_TAC] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC]);
```

### Informal statement
For all natural numbers `n` and sets `s` of size `n`, the number of derangements of `s` is equal to the `n`-th derangement number. A derangement of a set `s` is a permutation of the elements of `s` such that no element is mapped to itself.

### Informal sketch
The proof of `NUMBER_OF_DERANGEMENTS` involves:
* Using mathematical induction on the size `n` of the set `s`.
* Considering the base cases where `n` is 0 or 1.
* For the inductive step, assuming the result holds for sets of size `n` and proving it for sets of size `n + 1`.
* Using the `DERANGEMENT_INDUCT` tactic to perform the induction.
* Applying the `MATCH_MP_TAC` tactic to apply the `DERANGEMENT_ADD1` and `DERANGEMENT_ADD2` theorems.
* Using the `REWRITE_TAC` tactic to simplify the goal and the `CONJ_TAC` tactic to split the goal into two subgoals.
* Employing the `X_GEN_TAC` tactic to introduce new variables and the `SUBGOAL_THEN` tactic to assume and then discharge hypotheses.
* Utilizing the `REPEAT` and `STRIP_TAC` tactics to simplify the goal and the `FIRST_X_ASSUM` tactic to select and apply assumptions.
* The `HAS_SIZE_UNION` and `HAS_SIZE_IMAGE_INJ` theorems are used to reason about the size of sets and the injectivity of functions.

### Mathematical insight
The `NUMBER_OF_DERANGEMENTS` theorem provides a formula for calculating the number of derangements of a set of size `n`. This formula is based on the recursive relationship between the number of derangements of sets of size `n` and `n + 1`. The theorem has applications in combinatorics and probability theory.

### Dependencies
* `DERANGEMENT_INDUCT`
* `DERANGEMENT_ADD1`
* `DERANGEMENT_ADD2`
* `HAS_SIZE_UNION`
* `HAS_SIZE_IMAGE_INJ`
* `SELECT_UNIQUE`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the use of the `DERANGEMENT_INDUCT` tactic and the `MATCH_MP_TAC` tactic to apply the `DERANGEMENT_ADD1` and `DERANGEMENT_ADD2` theorems. The `REWRITE_TAC` and `CONJ_TAC` tactics should be replaced with equivalent tactics in the target proof assistant. Additionally, the `X_GEN_TAC` and `SUBGOAL_THEN` tactics may need to be replaced with equivalent tactics for introducing and discharging hypotheses.

---

## SUM_1

### Name of formal statement
SUM_1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUM_1 = prove
 (`sum(0..1) f = f 0 + f 1`,
  REWRITE_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0])
```

### Informal statement
For any function f, the sum of f over the interval from 0 to 1 is equal to the sum of f(0) and f(1).

### Informal sketch
* The proof involves rewriting the sum using `SUM_CLAUSES_NUMSEG`, which is a theorem that provides a way to expand summations over numeric segments.
* The `num_CONV `1`` tactic is used to convert the numeral 1 to its internal representation, which is necessary for the `SUM_CLAUSES_NUMSEG` theorem to apply.
* The `LE_0` theorem is also used, which states that 0 is less than or equal to any number, to establish the lower bound of the summation.
* The `REWRITE_TAC` tactic is used to apply these theorems and simplify the expression, ultimately showing that the sum of f over the interval from 0 to 1 is equal to f(0) + f(1).

### Mathematical insight
This theorem provides a basic property of summations, allowing us to simplify the sum of a function over a small interval. It is likely used as a building block for more complex results involving summations.

### Dependencies
* `SUM_CLAUSES_NUMSEG`
* `num_CONV`
* `LE_0`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the equivalent of `SUM_CLAUSES_NUMSEG` and `LE_0` are available and correctly applied. Additionally, the representation of numerals and the `REWRITE_TAC` tactic may need to be adapted to the target system.

---

## SUM_2

### Name of formal statement
SUM_2

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUM_2 = prove
 (`sum(0..2) f = f 0 + f 1 + f 2`,
  SIMP_TAC[num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0;
           REAL_ADD_AC])
```

### Informal statement
For any function `f`, the sum of `f` from `0` to `2` is equal to `f(0) + f(1) + f(2)`.

### Informal sketch
* The proof involves simplifying the expression `sum(0..2) f` using the `SUM_CLAUSES_NUMSEG` rule, which expands the summation into individual terms.
* The `SIMP_TAC` tactic is applied with various conversion rules (`num_CONV `2`` and `num_CONV `1``) to simplify the numerical expressions.
* The `LE_0` and `REAL_ADD_AC` rules are also used to handle ordering and associativity of addition, respectively.
* The overall strategy is to reduce the summation to a simple arithmetic expression by applying these rules and simplifications.

### Mathematical insight
This statement provides a basic property of summation, allowing the expansion of a finite sum into a series of individual terms. It is a fundamental step in many mathematical derivations and is used to establish more complex properties of summations.

### Dependencies
* `SUM_CLAUSES_NUMSEG`
* `LE_0`
* `REAL_ADD_AC`
* `num_CONV`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of summations and the specific rules used for simplification. The `SIMP_TAC` tactic and its associated conversion rules may need to be replaced with equivalent mechanisms in the target system. Additionally, the `SUM_CLAUSES_NUMSEG` rule may need to be defined or imported from a relevant library.

---

## DERANGEMENTS

### Name of formal statement
DERANGEMENTS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DERANGEMENTS = prove
 (`!n. ~(n = 0)
       ==> &(derangements n) =
           &(FACT n) * sum(0..n) (\k. --(&1) pow k / &(FACT k))`,
  MATCH_MP_TAC DERANGEMENT_INDUCT THEN REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[derangements; SUM_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[derangements; ARITH; SUM_2; SUM_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = (n + 1) + 1`] THEN
  SIMP_TAC[SUM_ADD_SPLIT; LE_0; SUM_SING_NUMSEG] THEN
  REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[real_pow] THEN REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD] THEN
  MP_TAC(SPEC `n:num` FACT_LT) THEN UNDISCH_TAC `~(n = 0)` THEN
  REWRITE_TAC[GSYM LT_NZ; REAL_POW_NEG; GSYM REAL_OF_NUM_LT; REAL_POW_ONE] THEN
  CONV_TAC REAL_FIELD)
```

### Informal statement
For all non-zero natural numbers `n`, the number of derangements of `n` objects is equal to `n` factorial multiplied by the sum from `0` to `n` of `(-1)` raised to the power of `k`, divided by `k` factorial.

### Informal sketch
* The proof starts by using `DERANGEMENT_INDUCT` to establish the base case and inductive step for the derangement formula.
* It then applies various rewrite rules (`REWRITE_TAC`) to simplify expressions involving `derangements`, `SUM_1`, `ADD_EQ_0`, and `ARITH_EQ`.
* The proof uses `CONV_TAC` with `NUM_REDUCE_CONV` and `REAL_RAT_REDUCE_CONV` to perform numerical and rational reductions.
* It introduces a variable `n` of type `num` using `X_GEN_TAC` and considers cases based on whether `n` is equal to `0` using `ASM_CASES_TAC`.
* For non-zero `n`, it applies further rewrite rules and simplifications, including those related to `REAL_OF_NUM_MUL`, `REAL_OF_NUM_ADD`, and `FACT`.
* The proof also employs `MP_TAC` with `FACT_LT` to utilize a fact about factorials and applies `UNDISCH_TAC` to utilize the assumption that `n` is not equal to `0`.
* Key HOL Light terms involved include `derangements`, `FACT`, `SUM_1`, and `REAL_POW`.

### Mathematical insight
This theorem provides a formula for calculating the number of derangements of `n` objects, which is a fundamental concept in combinatorial mathematics. The formula involves a sum of terms that represent the inclusion-exclusion principle, which is used to count the number of permutations that do not have any fixed points. The theorem is important because it provides a way to calculate the number of derangements exactly, which has applications in various fields such as statistics, computer science, and mathematics.

### Dependencies
* Theorems:
	+ `DERANGEMENT_INDUCT`
	+ `FACT_LT`
* Definitions:
	+ `derangements`
	+ `FACT`
	+ `SUM_1`
* Inductive rules: None

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the `derangements` function and the `FACT` function are defined correctly. Additionally, the use of `CONV_TAC` with `NUM_REDUCE_CONV` and `REAL_RAT_REDUCE_CONV` may need to be replaced with equivalent tactics in the target proof assistant. The `MP_TAC` and `UNDISCH_TAC` tactics may also require special handling, as they are used to apply a fact about factorials and utilize an assumption, respectively.

---

## DERANGEMENTS_EXP

### Name of formal statement
DERANGEMENTS_EXP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DERANGEMENTS_EXP = prove
 (`!n. ~(n = 0)
       ==> let e = exp(&1) in
           abs(&(derangements n) - &(FACT n) / e) < &1 / &2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DERANGEMENTS; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[real_div; GSYM REAL_EXP_NEG] THEN ASM_CASES_TAC `n < 5` THENL
   [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
     (ARITH_RULE `n < 5 ==> n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4`)) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC(map (num_CONV o mk_small_numeral) (1--5)) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `abs x < a <=> --a < x /\ x < a`] THEN
    REWRITE_TAC[real_sub] THEN CONJ_TAC THEN CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`-- &1`; `n + 1`] MCLAURIN_EXP_LE) THEN
  SIMP_TAC[PSUM_SUM_NUMSEG; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[ARITH_RULE `(0 + n + 1) - 1 = n`; GSYM real_div] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_ARITH `abs(a * b - a * (b + c)) = abs(a * c)`] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NEG] THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  SIMP_TAC[REAL_OF_NUM_LT; FACT_LT; REAL_FIELD
   `&0 < a ==> a * b / ((&n + &1) * a) = b / (&n + &1)`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[real_abs; REAL_EXP_POS_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp(&1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    UNDISCH_TAC `abs(u) <= abs(-- &1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&3` THEN CONJ_TAC THENL
   [CONV_TAC REALCALC_REL_CONV; ALL_TAC] THEN
  UNDISCH_TAC `~(n < 5)` THEN REWRITE_TAC[NOT_LT; GSYM REAL_OF_NUM_LE] THEN
  REAL_ARITH_TAC)
```

### Informal statement
For all non-zero natural numbers `n`, let `e` be the exponential of 1. Then the absolute difference between the number of derangements of `n` objects and the factorial of `n` divided by `e` is less than 1/2.

### Informal sketch
* The proof starts by considering the case when `n` is less than 5, in which it uses `DERANGEMENTS` and `FACT` to compute the derangements and factorial directly.
* For `n` greater than or equal to 5, it uses the `MCLAURIN_EXP_LE` theorem to establish a bound on the exponential function.
* The proof then applies various simplifications and rewriting using `REAL_ARITH`, `REAL_ABS`, and `REAL_EXP` properties to manipulate the expression and establish the desired inequality.
* Key steps involve choosing a real number `u` and using its properties to simplify the absolute difference expression.
* The proof also employs `REAL_LET_TRANS` and `REAL_LTE_TRANS` to establish the final inequality.

### Mathematical insight
This theorem provides an approximation of the number of derangements of `n` objects in terms of the exponential function and factorial. The key insight is that for sufficiently large `n`, the number of derangements can be approximated by `n! / e`, where `e` is the base of the natural logarithm. This approximation is useful in combinatorial calculations and has implications for understanding the asymptotic behavior of derangements.

### Dependencies
* Theorems:
  + `MCLAURIN_EXP_LE`
  + `REAL_EXP_POS_LE`
  + `REAL_LET_TRANS`
  + `REAL_LTE_TRANS`
* Definitions:
  + `DERANGEMENTS`
  + `FACT`
  + `REAL_EXP`
  + `REAL_ABS`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of real numbers, absolute values, and exponential functions. The `REAL_ARITH` and `REAL_ABS` properties may need to be replaced with equivalent properties in the target system. Additionally, the `MCLAURIN_EXP_LE` theorem may require a different formulation or proof in the target system.

---

## round

### Name of formal statement
round

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let round = new_definition
 `round x = @n. integer(n) /\ n - &1 / &2 <= x /\ x < n + &1 / &2`;;
```

### Informal statement
The `round` function is defined as a relation between a real number `x` and an integer `n`, such that `n` is an integer and `x` is within the range of `n - 1/2` to `n + 1/2`, inclusive on the lower bound and exclusive on the upper bound.

### Informal sketch
* The definition of `round` involves an existential quantification `@n` over the integers, indicating that for a given `x`, there exists an integer `n` that satisfies the given conditions.
* The condition `integer(n)` ensures that `n` is indeed an integer.
* The inequalities `n - &1 / &2 <= x` and `x < n + &1 / &2` define the rounding interval around `n`.
* The definition implies that `x` is rounded to the nearest integer `n` if it falls within this interval.

### Mathematical insight
The `round` function is a canonical construction in mathematics, particularly in real analysis and numerical computation. It represents the process of rounding a real number to the nearest integer, which is essential in various mathematical and computational contexts. The definition provided ensures that the rounding is done in a way that is consistent with standard rounding conventions.

### Dependencies
* `integer`
* `&1` and `&2` (likely representing the constants 1 and 2, respectively)

### Porting notes
When porting this definition to other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles existential quantification, real numbers, and integers. Specifically, ensure that the ported definition correctly captures the rounding interval and the integer condition. Additionally, be mindful of any differences in how these systems handle division and inequality, as these are crucial to the definition of `round`.

---

## ROUND_WORKS

### Name of formal statement
ROUND_WORKS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ROUND_WORKS = prove
 (`!x. integer(round x) /\ round x - &1 / &2 <= x /\ x < round x + &1 / &2`,
  GEN_TAC THEN REWRITE_TAC[round] THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `floor(x + &1 / &2)` THEN MP_TAC(SPEC `x + &1 / &2` FLOOR) THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC)
```

### Informal statement
For all real numbers x, the `round` of x is an integer, and x is bounded by `round x - 1/2` and `round x + 1/2`.

### Informal sketch
* The proof starts by assuming an arbitrary real number `x`.
* It then applies the definition of `round` and uses `CONV_TAC` to set up the inequality.
* The `EXISTS_TAC` introduces a witness, `floor(x + 1/2)`, to establish the relationship between `x` and its `round` value.
* The proof then uses `MP_TAC` with `FLOOR` to derive properties about the floor function.
* Simplifications using `SIMP_TAC` with `INTEGER_CLOSED` help to establish the integer nature of `round x`.
* Finally, `REAL_ARITH_TAC` is used to finalize the real arithmetic inequalities.

### Mathematical insight
This theorem provides a key property of the `round` function, establishing that it rounds a real number to the nearest integer, with ties going to the nearest even integer. The `round` function is essential in many mathematical and computational contexts, and this theorem helps to formalize its behavior.

### Dependencies
* `round`
* `FLOOR`
* `INTEGER_CLOSED`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to the handling of the `round` function and the `floor` function, as their implementations may differ. Additionally, the use of `REAL_ARITH_TAC` may need to be replaced with equivalent tactics or libraries for real arithmetic in the target system.

---

## DERANGEMENTS_EXP

### Name of formal statement
DERANGEMENTS_EXP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DERANGEMENTS_EXP = prove
 (`!n. ~(n = 0)
       ==> let e = exp(&1) in &(derangements n) = round(&(FACT n) / e)`,
  REPEAT STRIP_TAC THEN LET_TAC THEN
  MATCH_MP_TAC REAL_EQ_INTEGERS_IMP THEN
  REWRITE_TAC[INTEGER_CLOSED; ROUND_WORKS] THEN
  MP_TAC(SPEC `&(FACT n) / e` ROUND_WORKS) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DERANGEMENTS_EXP) THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REAL_ARITH_TAC)
```

### Informal statement
For all non-zero natural numbers n, the number of derangements of n elements is equal to the rounded value of the factorial of n divided by the exponential of 1.

### Informal sketch
* The proof starts by assuming a non-zero natural number `n`.
* It defines `e` as the exponential of 1 and uses this to express the number of derangements of `n` elements in terms of `n` and `e`.
* The proof involves applying several key steps:
  + Using `REAL_EQ_INTEGERS_IMP` to relate real and integer equality
  + Applying `ROUND_WORKS` to justify rounding operations
  + Employing `MATCH_MP_TAC` and `MP_TAC` to apply relevant theorems and lemmas
  + Simplifying expressions using `REWRITE_TAC` and `ASM_REWRITE_TAC`
  + Performing real arithmetic using `REAL_ARITH_TAC`
* These steps ultimately establish the relationship between the number of derangements, the factorial of `n`, and the exponential of 1.

### Mathematical insight
This theorem provides an approximate formula for the number of derangements of a set with `n` elements, relating it to the factorial of `n` and the exponential function. This connection is significant because it offers a way to compute or approximate the number of derangements using well-known mathematical functions.

### Dependencies
* Theorems:
  + `REAL_EQ_INTEGERS_IMP`
  + `ROUND_WORKS`
* Definitions:
  + `derangements`
  + `FACT`
  + `exp`
* Other:
  + `LET_DEF`
  + `LET_END_DEF`
  + `INTEGER_CLOSED`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to handling the `ROUND_WORKS` theorem and the `REAL_EQ_INTEGERS_IMP` theorem, as these may have different formulations or requirements in other systems. Additionally, the use of `MATCH_MP_TAC` and `MP_TAC` may need to be adapted based on the target system's tactic language and support for automation.

---

## THE_DERANGEMENTS_FORMULA

### Name of formal statement
THE_DERANGEMENTS_FORMULA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let THE_DERANGEMENTS_FORMULA = prove
 (`!n s. s HAS_SIZE n /\ ~(n = 0)
         ==> FINITE {p | p deranges s} /\
             let e = exp(&1) in
             &(CARD {p | p deranges s}) = round(&(FACT n) / e)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP NUMBER_OF_DERANGEMENTS) THEN
  ASM_SIMP_TAC[HAS_SIZE; DERANGEMENTS_EXP])
```

### Informal statement
For all natural numbers `n` and sets `s` of size `n`, where `n` is not equal to 0, it holds that the set of permutations that derange `s` is finite, and the cardinality of this set is equal to the rounded value of the factorial of `n` divided by the exponential of 1.

### Informal sketch
* The proof starts by assuming `n` and `s` such that `s` has size `n` and `n` is not 0.
* It then applies the `NUMBER_OF_DERANGEMENTS` theorem to establish a relationship between the number of derangements of `s` and the factorial of `n`.
* The `REPEAT STRIP_TAC` and `FIRST_X_ASSUM(MP_TAC o MATCH_MP NUMBER_OF_DERANGEMENTS)` steps are used to apply this theorem and perform the necessary logical transformations.
* The `ASM_SIMP_TAC[HAS_SIZE; DERANGEMENTS_EXP]` step simplifies the expression using the definitions of `HAS_SIZE` and `DERANGEMENTS_EXP`.
* The key idea is to relate the number of derangements to the exponential of 1 and the factorial of `n`, and to show that this relationship holds for any set `s` of size `n`.

### Mathematical insight
This theorem provides a formula for the number of derangements of a set of size `n`, which is a fundamental concept in combinatorics. The formula involves the exponential of 1 and the factorial of `n`, which are both well-studied mathematical functions. The theorem is important because it provides a precise and efficient way to calculate the number of derangements, which has applications in various areas of mathematics and computer science.

### Dependencies
* `NUMBER_OF_DERANGEMENTS`
* `HAS_SIZE`
* `DERANGEMENTS_EXP`
* `FACT`
* `exp`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `NUMBER_OF_DERANGEMENTS` theorem is properly translated and that the `REPEAT STRIP_TAC` and `FIRST_X_ASSUM(MP_TAC o MATCH_MP NUMBER_OF_DERANGEMENTS)` steps are replaced with equivalent tactics in the target system. Additionally, the `ASM_SIMP_TAC[HAS_SIZE; DERANGEMENTS_EXP]` step may need to be modified to accommodate differences in the way the target system handles simplification and rewriting.

---

