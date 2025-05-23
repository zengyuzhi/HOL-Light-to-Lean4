# derangements.ml

## Overview

Number of statements: 43

`derangements.ml` formalizes the concept of derangements and provides a formula to calculate their number. It imports libraries for transcendental functions, real number arithmetic, and the floor function. The file proves that the number of derangements of a set of size *n* is the nearest integer to *n!/e*.


## domain

### Name of formal statement
domain

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let domain = new_definition
 `domain r = {x | ?y. r(x,y)}`;;
```

### Informal statement
The domain of a relation `r` is defined as the set of all `x` such that there exists a `y` for which the relation `r(x, y)` holds.

### Informal sketch
The definition introduces `domain` as a set constructor. Given a binary relation `r`, `domain r` is defined as the set of all first elements `x` for which there exists a second element `y` such that `r(x, y)` holds.
The proof of the definition's consistency is handled automatically by the definitional mechanism in HOL Light.

### Mathematical insight
The domain of a relation is a fundamental concept in set theory and is used to describe the set of elements on which the relation acts. This definition provides a formal way to represent this concept within HOL Light.

### Dependencies
None.

### Porting notes (optional)
The definition should be straightforward to port to other proof assistants, as it relies only on basic set theory and predicate logic. Ensure that the target system supports set comprehension (`{x | P x}`) and existential quantification (`?y. P y`).


---

## range

### Name of formal statement
range

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let range = new_definition
 `range r = {y | ?x. r(x,y)}`;;
```
### Informal statement
The range of a relation `r` is defined to be the set of all `y` such that there exists an `x` for which the pair `(x, y)` is in the relation `r`.

### Informal sketch
The definition introduces the term `range r` as syntactic sugar for `{y | ?x. r(x,y)}`. It involves creating a new definition using `new_definition`, thereby associating the term `range r` with the set of all `y` such that there exists an `x` where `r(x, y)` holds. The underlying mechanism involves standard definition introduction.

### Mathematical insight
The `range` of a relation is a fundamental concept in set theory and is closely related to the codomain of a function. It represents the set of all second elements in the pairs of the relation. This definition provides a formal way to refer to and reason about the set of all "outputs" of a relation.

### Dependencies
None

### Porting notes (optional)
In other provers like Coq or Lean, this definition would correspond to defining a new function `range` that takes a relation as input and returns a set containing all elements `y` for which there exists `x` such that `r(x, y)` holds. The specific syntax for set comprehension may differ.


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
For any set `s`, the relation `id(s)` holds between `x` and `y` if and only if `x` is an element of `s` and `x` is equal to `y`.

### Informal sketch
The definition introduces the identity relation on a set `s`. Given elements `x` and `y`, `id(s)(x, y)` is true if and only if `x` belongs to the set `s` and `x` equals `y`. This relation captures the notion of equality within the specific domain defined by set `s`.

### Mathematical insight
The `id` definition introduces the identity relation on a set. The identity relation is a fundamental concept in mathematics. Restricting the identity relation to a particular set `s` is a common operation in set theory and type theory, used wherever a specific domain is required.

### Dependencies
None

---
### Name of formal statement
compose

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let id = new_definition
 `id(s) (x,y) <=> x IN s /\ x = y`;;
```

### Informal statement
For any relations `r` and `s`, the relation `(r % s)` holds between `x` and `y` if and only if there exists a `z` such that `r` holds between `x` and `z`, and `s` holds between `z` and `y`.

### Informal sketch
The definition introduces relational composition.  The relational composition of `r` and `s`, denoted `r % s`, relates `x` to `y` if there exists an intermediate element `z` such that `x` is related to `z` by `r` and `z` is related to `y` by `s`. This `z` acts as a "bridge" element between `x` and `y`. The definition uses existential quantification (`?z`) to assert the existence of such an element.

### Mathematical insight
Relational composition is a fundamental operation in the theory of relations, and it plays a vital role in various areas of mathematics and computer science as it expresses sequential application or chaining of relations.

### Dependencies
None


---

## converse

### Name of formal statement
converse

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let converse = new_definition
 `converse(r) (x,y) = r(y,x)`;;
```

### Informal statement
The converse of a binary relation `r` is defined such that the converse of `r` applied to the pair `(x, y)` is equivalent to `r` applied to the pair `(y, x)`.

### Informal sketch
- The definition introduces a new function `converse` that takes a relation `r` as input.
-  The value of `converse(r)` when applied to a pair `(x, y)` is defined to be the result of applying `r` to the reversed pair `(y, x)`.
-  This definition directly captures the standard notion of a converse relation.

### Mathematical insight
The `converse` relation is a fundamental concept in set theory and logic. It provides a way to reverse the direction of a relation. This definition is a direct formalization of the standard mathematical definition of a converse relation. The converse of a relation `r` swaps the order of the elements in each pair that satisfies `r`.

### Dependencies
None


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
The function `swap`, when applied to two values `a` and `b` and a pair of values `(x, y)`, returns true if and only if `x` equals `a` and `y` equals `b`, or `x` equals `b` and `y` equals `a`.

### Informal sketch
- The definition introduces `swap` as a function that takes two arguments, `a` and `b`, and returns another function that takes a pair `(x, y)` as input.
- A key step is to define the condition under which `swap(a, b) (x, y)` holds. This is essentially defining a transposition.
- The condition is that the pair `(x, y)` is either equal to `(a, b)` or `(b, a)`. This is expressed using the logical connective "or" (`\/`).
- The equality of pairs is broken down into the conjunction of the equality of their components, using the logical connective "and" (`/\`).

### Mathematical insight
The definition of `swap` captures the notion of swapping two elements. When applied to a pair `(x, y)`, it checks whether `(x, y)` is either `(a, b)` or `(b, a)`. It's a basic but fundamental concept in mathematics and computer science, often used to define permutations or transpositions.

### Dependencies
None


---

## REL_TAC

### Name of formal statement
REL_TAC

### Type of the formal statement
Tactic

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
  ASM_MESON_TAC[];;
```
### Informal statement
`REL_TAC` is a tactic in HOL Light that simplifies goals involving relations by rewriting with properties of functions, sets, pairs, relations, and set operations, and then using automated tactics like stripping quantifiers and applying assumptions to discharge the goal.

### Informal sketch
The tactic `REL_TAC` is designed to automatically prove or simplify theorems involving relations by performing several layers of rewriting and simplification:
- Pop all assumptions and apply `ALL_TAC`.
- Rewrite using properties of functions (`FUN_EQ_THM`), pairs (`FORALL_PAIR_THM`, `EXISTS_PAIR_THM`, `PAIR_BETA_THM`), and definitions of functions and relations like `permutes`, `pairsup`, `domain`, `range`, `compose`, `id`, `converse`, `swap`, `deranges` and set operations such as `IN_INSERT`, `IN_DELETE`, `NOT_IN_EMPTY`, `IN_ELIM_THM`.
- Rewrite using properties of sets (`IN`, `EMPTY`, `INSERT`, `DELETE`, `UNION`, `IN_ELIM_THM`), pairs (`PAIR_EQ`) and relation operations (`id`, `converse`, `swap`).
- Simplify the goal by repeatedly stripping quantifiers (`STRIP_TAC`) or splitting equations (`EQ_TAC`).
- Repeatedly substitute universally quantified variables from assumptions where the left-hand side of an assumption's conclusion matches the variable and where the right-hand side of an assumption's conclusion matches the variable.
- Call the `ASM_MESON_TAC` to attempt to discharge the goal using the assumptions.

### Mathematical insight
This tactic attempts to automate proofs about relations. It leverages the definitions of relation operations, set operations, and the properties of pairing to rewrite the goal into a simpler form that can be solved by generic automated tactics like `ASM_MESON_TAC`.

### Dependencies
- `FUN_EQ_THM`
- `FORALL_PAIR_THM`
- `EXISTS_PAIR_THM`
- `PAIR_BETA_THM`
- `permutes`
- `pairsup`
- `domain`
- `range`
- `compose`
- `id`
- `converse`
- `swap`
- `deranges`
- `IN_INSERT`
- `IN_DELETE`
- `NOT_IN_EMPTY`
- `IN_ELIM_THM`
- `IN`
- `EMPTY`
- `INSERT`
- `DELETE`
- `UNION`
- `IN_ELIM_THM`
- `PAIR_EQ`


---

## REL_RULE

### Name of formal statement
REL_RULE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REL_RULE tm = prove(tm,REL_TAC);;
```
### Informal statement
The theorem `REL_RULE` states that for any term `tm`, the goal `tm` can be proven using the tactic `REL_TAC`. In other words, `REL_REL` establishes `tm` as a theorem.

### Informal sketch
- Apply the tactic `REL_TAC` to the term `tm`.
- The tactic `REL_TAC` is assumed to perform the necessary steps to prove the term `tm`.
- If `REL_TAC` succeeds, the term `tm` is established as a theorem.

### Mathematical insight
The theorem `REL_RULE` represents a rule of inference or a pre-proven result that can be directly applied to establish the truth of a term. The key insight is trusting the tactic `REL_TAC` which presumably encapsulates a specific proof method or axiom application. The theorem itself simply wraps the application of this tactic and makes it a reusable theorem.

### Dependencies
- Tactic: `REL_TAC`
- Function: `prove`

### Porting notes (optional)
The main difficulty here is understanding and reimplementing the tactic `REL_TAC`. To port this, one must:
1. Analyze the HOL Light implementation of `REL_TAC`.
2. Identify the logical steps it performs.
3. Recreate these steps using tactics and rules of inference in the target proof assistant.
The `prove` function in HOL Light automatically handles proof management, which you may need to replicate using the target's proof script mechanisms.


---

## CONVERSE_COMPOSE

### Name of formal statement
CONVERSE_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONVERSE_COMPOSE = prove
 (`!r s. converse(r % s) = converse(s) % converse(r)`,
  REL_TAC);;
```

### Informal statement
For all relations `r` and `s`, the converse of the composition of `r` and `s` is equal to the composition of the converse of `s` and the converse of `r`.

### Informal sketch
The proof proceeds automatically using `REL_TAC`. This tactic likely expands the definitions of `converse` and relation composition (`%`) and applies simplification rules for set theory to arrive at the result.

*   Expand the definition of `converse(r % s)` using the definition of relation composition.
*   Expand the definition of `converse` on the resulting expression.
*   Expand the definition of `converse(s) % converse(r)` using the definition of relation composition.
*   Expand the definition of `converse` on `s` and `r`.
*   Show that the two resulting expressions are equivalent by appealing to the equivalence of the underlying sets.

### Mathematical insight
This theorem states how the converse operation interacts with relation composition. It's a fundamental property in relational algebra, analogous to how the inverse of a product of matrices is the product of the inverses in reverse order.

### Dependencies
*   `converse`
*   `%` (relation composition)

### Porting notes (optional)
This theorem should be straightforward to port to other proof assistants since it involves standard definitions of relation composition and converse. The main challenge might be ensuring that the definitions of `converse` and relation composition are compatible.


---

## CONVERSE_CONVERSE

### Name of formal statement
CONVERSE_CONVERSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONVERSE_CONVERSE = prove
 (`!r. converse(converse r) = r`,
  REL_TAC);;
```
### Informal statement
For all binary relations `r`, the converse of the converse of `r` is equal to `r`.

### Informal sketch
The proof of `!r. converse(converse r) = r` is done using the `REL_TAC` tactic. This tactic automatically proves basic theorems about relations. The core idea relies on the definition of `converse` and relational equality.
- The definition of `converse r` is `{(y, x) | (x, y) ∈ r}`.
- Therefore, `converse(converse r)` is `{(x, y) | (y, x) ∈ converse r}` which simplifies to `{(x, y) | (x, y) ∈ r}`.
- Relational equality in HOL Light is extensional; that is, two relations are equal if they contain the same pairs. Since `{(x, y) | (x, y) ∈ r}` represents the same set of pairs as `r`, the equality holds.

### Mathematical insight
The theorem `CONVERSE_CONVERSE` states a fundamental property of the `converse` operation on binary relations: applying the converse operation twice returns the original relation. This property demonstrates the involutive nature of the converse operation. It is essential for reasoning about relations and their inverses, and for simplifying expressions involving relational algebra. It highlights how symmetry is recovered when applied twice.

### Dependencies
- Tactics: `REL_TAC`


---

## PAIRSUP_EXPLICIT

### Name of formal statement
PAIRSUP_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_EXPLICIT = prove
 (`!p s t.
        p pairsup (s,t) <=>
        (!x y. p(x,y) ==> x IN s /\ y IN t) /\
        (!x. x IN s ==> ?!y. y IN t /\ p(x,y)) /\
        (!y. y IN t ==> ?!x. x IN s /\ p(x,y))`,
  REL_TAC);;
```

### Informal statement
For all binary relations `p` and sets `s` and `t`, `p` is a pairing relation between `s` and `t` if and only if:
1. For all `x` and `y`, if `p(x, y)` holds, then `x` is in `s` and `y` is in `t`.
2. For all `x`, if `x` is in `s`, then there exists a unique `y` such that `y` is in `t` and `p(x, y)` holds.
3. For all `y`, if `y` is in `t`, then there exists a unique `x` such that `x` is in `s` and `p(x, y)` holds.

### Informal sketch
The theorem explicitly defines what it means for a binary relation `p` to be a pairing between two sets `s` and `t`. The proof is conducted using `REL_TAC`, which essentially performs relational reasoning.

*   The theorem states that a relation `p` relates `s` to `t` (`p pairsup (s,t)`) if and only if three main properties hold:
    *   All pairs related by `p` must have their first element in `s` and their second element in `t`.
    *   Every element in `s` must be related via `p` to a unique element in `t`.
    *   Every element in `t` must be related via `p` to a unique element in `s`.

### Mathematical insight
The theorem provides a direct definition of `pairsup` that emphasizes the one-to-one correspondence between elements of `s` and `t` through the relation `p`. This explicit characterization, involving membership constraints and unique existence, facilitates reasoning about bijections established by `p`. It's a stricter requirement than just requiring `p` to be a subset of the Cartesian product `s` x `t`.

### Dependencies
*   `pairsup`
*   `IN`
*   `REL_TAC`


---

## PERMUTES_EXPLICIT

### Name of formal statement
PERMUTES_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_EXPLICIT = prove
 (`!p s. p permutes s <=>
         (!x y. p(x,y) ==> x IN s /\ y IN s) /\
         (!x. x IN s ==> ?!y. y IN s /\ p(x,y)) /\
         (!y. y IN s ==> ?!x. x IN s /\ p(x,y))`,
  REL_TAC);;
```

### Informal statement
For all binary relations `p` and sets `s`, `p` is a permutation on `s` if and only if the following conditions hold:
1. For all `x` and `y`, if `p(x, y)` then `x` is in `s` and `y` is in `s`.
2. For all `x`, if `x` is in `s`, then there exists a unique `y` such that `y` is in `s` and `p(x, y)`.
3. For all `y`, if `y` is in `s`, then there exists a unique `x` such that `x` is in `s` and `p(x, y)`.

### Informal sketch
The proof uses `REL_TAC`, indicating that it reasons directly about the relational definition of permutations.

*   The intention is likely to unfold or rewrite the definition of `permutes` relation and then to reason about the conditions relating elements via the permutation.
*   The forward direction proves that if `p` permutes `s`, then all three conditions about existing elements within `s` and having unique pairings must hold.
*   The reverse direction shows that satisfying those element/pairing requirements is sufficient to show `p` is a permutation over `s`.

### Mathematical insight
This theorem provides an explicit characterization of what it means for a relation `p` to be a permutation on a set `s`. It states that a permutation on a set `s` is a binary relation `p` such that it relates each element of `s` to a unique element of `s` and each element of `s` is related to by a unique element of `s`. This theorem is important as it connects the abstract notion of permutation (as a binary relation) to more concrete conditions about elements and their pairings.

### Dependencies
*   `permutes`
*   `IN`

### Porting notes (optional)
The use of `REL_TAC` suggests a direct manipulation of relations, and may require different techniques in systems where relational reasoning is less developed. The target assistant needs to have a well-defined notion of binary relations and sets, and a way to express unique existence (`?!`).


---

## PAIRSUP_DOMRAN

### Name of formal statement
PAIRSUP_DOMRAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_DOMRAN = prove
 (`!p s t. p pairsup (s,t) ==> domain p = s /\ range p = t`,
  REL_TAC);;
```
### Informal statement
For all relations `p` and sets `s` and `t`, if `p` pairs up the sets `s` and `t`, then the domain of `p` is equal to `s` and the range of `p` is equal to `t`.

### Informal sketch
The theorem states a property about relations that "pair up" two sets, asserting that the domain and range of the pairing relation must be identical to the sets being paired. The proof is accomplished using the tactic `REL_TAC`, which, in HOL Light, likely involves rewriting with the definitions of `pairsup`, `domain`, and `range` and then using basic set-theoretic reasoning to show the equivalence.

*   The proof likely starts by expanding the definition of `p pairsup (s, t)`, probably into `Every (destruct_pair (λx. &Fst x ∈ s ∧ &Snd x ∈ t)) p ∧ ∀x. x ∈ s ⇒ ∃y. (x, y) ∈ p ∧ y ∈ t ∧ ∀y'. (x, y') ∈ p ⇒ y' ∈ t ∧ ∀ y. y ∈ t ⇒ ∃ x. (x, y) ∈ p ∧ x ∈ s ∧ ∀ x'. (x', y) ∈ p ⇒ x' ∈ s`.
*   Then the definitions of `domain` and `range` need to be introduced: `domain p = {x | ∃y. (x,y) ∈ p}` and `range p = {y | ∃x. (x,y) ∈ p}`.
*   Finally, derive `domain p = s` and `range p = t` by rewriting definitions of set equality, domain, range, and pairs-up, and by applying basic set-theoretic inferences.

### Mathematical insight
The theorem `PAIRSUP_DOMRAN` is a fundamental property that connects the `pairsup` predicate with the standard set-theoretic notions of domain and range of a relation. Specifically, it ensures that if a relation `p` is said to 'pair up' the sets `s` and `t`, then `p` must exhaustively cover the elements within `s` as its domain and `t` as its range. This is important for reasoning about mappings and correspondences between sets in a rigorous way.

### Dependencies
- `pairsup`
- `domain`
- `range`
- `REL_TAC` (Tactic probably makes use of basic set theory theorems)


---

## PERMUTES_DOMRAN

### Name of formal statement
PERMUTES_DOMRAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_DOMRAN = prove
 (`!p s. p permutes s ==> domain p = s /\ range p = s`,
  REL_TAC);;
```
### Informal statement
For all permutations `p` and sets `s`, if `p` permutes `s`, then the domain of `p` equals `s` and the range of `p` equals `s`.

### Informal sketch
The proof uses `REL_TAC`, which likely expands the definition of `permutes` and performs basic rewriting and simplification using the definitions of `domain` and `range`.
- The predicate `p permutes s` means that `p` is a bijection from `s` to `s`.
- The domain of a permutation `p` refers to the set of elements for which `p` is defined.
- The range of a permutation `p` refers to the set of elements that are the image of some element under `p`.
- Because `p` is a bijection from `s` to `s`, every element in `s` has a unique image in `s` under `p`, and every element in `s` is the image of a unique element in `s` under `p`. Therefore, the domain and range of `p` both equal `s`.

### Mathematical insight
This theorem formalizes a fundamental property of permutations: a permutation of a set `s` maps the elements of `s` to elements of `s` in a bijective manner. As a corollary, if a mapping permutes a set, the domain and range must be identical to that set. This basic result is important in reasoning about permutations in algebra and combinatorics.

### Dependencies
- `permutes`
- `domain`
- `range`

### Porting notes (optional)
The definition of `permutes` is critical here, as different systems might have different ways of expressing the underlying bijection. Ensure that the definitions of `domain` and `range` are compatible with the notion of a function or relation being used.


---

## PAIRSUP_FUNCTIONAL

### Name of formal statement
PAIRSUP_FUNCTIONAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_FUNCTIONAL = prove
 (`!p s t. p pairsup (s,t) ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y'`,
  REL_TAC);;
```
### Informal statement
For all relations `p` and for all pairs `(s, t)`, if the relation `p` holds between each of `s` and `t`, then for all `x`, `y`, and `y'`, if `p` holds between `x` and `y`, and `p` holds between `x` and `y'`, then `y` is equal to `y'`.

### Informal sketch
- The proof uses `REL_TAC`, indicating it relies on relational reasoning.
- The theorem states that if a relation `p` relates a first element `s` to a second element `t` packaged in a pair `(s,t)`, then `p` must be functional. That is, for all `x`, `p` relates `x` to at most one `y`.

### Mathematical insight
The theorem `PAIRSUP_FUNCTIONAL` establishes a condition under which a relation is functional. It does so by requiring that the relation holds between the elements of a pair. This property can be used to prove that a given relation represents a (partial) function. The representation of functions as relations is common in formal mathematics because it allows for reasoning about functions even when they are not defined for all arguments.

### Dependencies
None

### Porting notes (optional)
The main challenge for porting this theorem might be finding an equivalent of the `REL_TAC` tactic in other provers. The porter may need to rely more on manual application of relational reasoning principles, or find an automated tactic to apply relational rules efficiently.


---

## PERMUTES_FUNCTIONAL

### Name of formal statement
PERMUTES_FUNCTIONAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_FUNCTIONAL = prove
 (`!p s. p permutes s ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y'`,
  REL_TAC);;
```
### Informal statement
For all relations `p` and sets `s`, if `p` permutes `s`, then for all `x`, `y`, and `y'`, if `p(x, y)` and `p(x, y')`, then `y = y'`.

### Informal sketch
The proof is done using `REL_TAC`, which is a tactic for reasoning about relations. The theorem essentially states that a permutation, when viewed as a relation, is a function. That is, if `p` permutes `s`, then for any `x` in `s`, `p` maps `x` to a unique `y` in `s`.

### Mathematical insight
The theorem captures the functional nature of permutations. A permutation is a bijection from a set to itself. This theorem formalizes the injectivity aspect of this bijection by specifying that for a given input, there is only one possible output. This is an important property when reasoning about permutations, as it ensures that the permutation is well-defined.

### Dependencies
- Definitions: `permutes`

### Porting notes (optional)
In translating this to other proof assistants, ensure that the definition of `permutes` is properly translated. The key is to express that a permutation, viewed as a relation, satisfies the property of being a function. Some proof assistants might require explicit unfolding of the definition of `permutes`.


---

## PAIRSUP_COFUNCTIONAL

### Name of formal statement
PAIRSUP_COFUNCTIONAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_COFUNCTIONAL = prove
 (`!p s t. p pairsup (s,t) ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x'`,
  REL_TAC);;
```
### Informal statement
For all relations `p`, and for all pairs `(s, t)`, if `p` relates the pair `(s, t)`, then for all `x`, `x'`, and `y`, if `p` relates `(x, y)` and `p` relates `(x', y)`, then `x` is equal to `x'`.

### Informal sketch
The theorem states that if a relation `p` relates pairs `(s, t)`, then `p` is cofunctional, meaning if `(x, y)` and `(x', y)` are both related by `p`, then `x` must be equal to `x'`. The proof is discharged by `REL_TAC`, an automatic tactic that reasons about relations, leveraging existing definitions and theorems about relations and pairs to establish the cofunctionality property based on the assumption `p pairsup (s, t)`.

### Mathematical insight
This theorem demonstrates a property of relations which relate pairs. It shows that if a relation `p` operates specifically on pairs (as indicated by `pairsup`), then `p` is cofunctional. Cofunctionality is a key property in the theory of functions and relations, often related to injectivity or well-definedness properties in a broader mathematical context.

### Dependencies
None

### Porting notes (optional)
The `REL_TAC` tactic is a HOL Light specific automated decision procedure for relations, so this proof may require a more involved decomposition in proof assistants lacking a comparable tactic. The specific definitions that `REL_TAC` uses to automatically discharge this theorem will need to be identified and used in the manual port.


---

## PERMUTES_COFUNCTIONAL

### Name of formal statement
PERMUTES_COFUNCTIONAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_COFUNCTIONAL = prove
 (`!p s. p permutes s ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x'`,
  REL_TAC);;
```
### Informal statement
For all permutations `p` and sets `s`, if `p` permutes `s`, then for all `x`, `x'`, and `y`, if `p(x,y)` and `p(x',y)` then `x = x'`.

### Informal sketch
The proof uses `REL_TAC`, which probably unfolds definitions related to `permutes` and then resolves the goal using properties of relations. The key idea is that a permutation, when viewed as a relation between two sets, must be a function when restricted to its domain. Specifically, the condition `p permutes s` implies that `p` is a function from `s` to `s`, ensuring that for any `y`, there can be only one `x` such that `p(x, y)`.

### Mathematical insight
The theorem states that a permutation, when viewed as a binary relation, is cofunctional. That is, if `p` permutes a set `s`, then `p` is a function from `s` to `s`. This expresses a key property of permutations: they are bijections, hence functions. This fact is used in reasoning about permutations.

### Dependencies
- Definition: `permutes`
- Tactic: `REL_TAC`


---

## PAIRSUP_ID

### Name of formal statement
PAIRSUP_ID

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_ID = prove
 (`!s. id(s) pairsup (s,s)`,
  REL_TAC);;
```

### Informal statement
For all sets `s`, the identity relation `id(s)` pairs up the set `s` with itself, i.e., `id(s)` is a pairing relation between `s` and `s`.

### Informal sketch
- The proof proceeds by applying the tactic `REL_TAC`.
- The core idea is that the identity relation on a set `s` relates each element of `s` only to itself.
- The `pairsup` relation holds between a relation `r` and two sets `s1` and `s2` if and only if the domain of `r` is `s1`, the range of `r` is `s2`, and `r` is a subset of the cartesian product of `s1` and `s2`.
- For `id(s)` to `pairsup (s,s)`, we need to confirm:
  - The domain of `id(s)` is `s`.
  - The range of `id(s)` is `s`.
  - `id(s)` is a subset of `s` × `s`.
- These directly follow from the definition of `id(s)`: `{(x, x) | x ∈ s}`.

### Mathematical insight
The identity relation on a set `s` trivially relates every element of `s` to itself. This theorem formalizes the basic and intuitive fact that such a relation constitutes a pairing between the set `s` and itself. This result is a basic sanity check on the definitions of `id` and `pairsup`.

### Dependencies
- `id` (definition of identity relation)
- `pairsup` (definition of pairing relation)

### Porting notes (optional)
- This theorem should be straightforward to prove in most proof assistants, as it primarily relies on unfolding definitions and basic set theory reasoning. The `REL_TAC` tactic in Hol Light likely handles these steps automatically.


---

## PERMUTES_ID

### Name of formal statement
PERMUTES_ID

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_ID = prove
 (`!s. id(s) permutes s`,
  REL_TAC);;
```

### Informal statement
For all sets `s`, the identity function `id` permutes `s`.

### Informal sketch
- The theorem states that applying the identity function `id` to any set `s` results in a permutation of `s`.
- The proof uses the tactic `REL_TAC`, which likely expands the definition of `permutes` and then simplifies the statement using properties of the identity function and set equality.
- The definition of `permutes` probably involves showing a bijection between the set `s` and the image of `s` under the function in question, which in this case is the identity function. Since the identity function maps every element in `s` to itself, the image of `s` under `id` is just `s`. Consequently, it suffices to show that there exists a bijection between `s` and `s`, which is trivially true using the identity function again.

### Mathematical insight
The theorem `PERMUTES_ID` demonstrates a fundamental property of permutations. A permutation is a rearrangement of elements of a set. The identity function, which leaves every element unchanged, trivially satisfies this condition because it simply maps each element to itself without altering the set's constitution. This theorem provides a simple but important example of a permutation, establishing that the identity function acts as a permutation for any set.

### Dependencies
- Definitions: `permutes`, `id`
- Theorems: principles of set theory and bijections needed to prove something permutes a set ( likely handled implicitly by `REL_TAC`).

### Porting notes (optional)
The primary challenge in porting this theorem lies in ensuring that the definition of `permutes` and `id` are correctly translated and that the target proof assistant can automatically handle the simplification steps (likely involving beta reduction and equational reasoning) required to prove the theorem after expanding the definitions. The `REL_TAC` tactic likely hides significant automation, so it may be necessary to unfold the definition of `permutes` and perform the proof manually, showing the required bijection.


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
  REL_TAC);;
```

### Informal statement
For any binary relation `p` and any terms `s` and `t`, if the relation `p` relates `s` and `t` under the `pairsup` relation, then the converse of the relation `p` relates `t` and `s` under the `pairsup` relation.

### Informal sketch
The proof is done using `REL_TAC`, which means it relies on the definition of `pairsup` and `converse` along with relational reasoning. The theorem states that if `p pairsup (s, t)` holds, then `converse(p) pairsup (t, s)` must also hold. The `REL_TAC` tactic likely unfolds the definitions of `pairsup` and `converse`, using the built-in relational calculus simplifications to show the implication holds directly.

### Mathematical insight
This theorem establishes a fundamental property of relations and their converses when paired with tuples. The `pairsup` relation lifts a binary relation to operate on pairs. This theorem demonstrates how the direction of the relation is reversed when both the relation and the tuple are reversed via `converse` and the tuple swap. This is crucial for reasoning about symmetry and duality within relational structures.

### Dependencies
Definitions:
- `pairsup`
- `converse`

Theorems:
- None

### Porting notes (optional)
The main challenge in porting this theorem lies in ensuring that the definitions of `pairsup` and `converse` are faithfully represented in the target proof assistant. The built-in automation via `REL_TAC` in HOL Light might need to be replicated using appropriate tactics and simplification rules in the target system. Specifically, the unfolding of definitions and applications of relational reasoning principles require careful consideration.


---

## PERMUTES_CONVERSE

### Name of formal statement
PERMUTES_CONVERSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_CONVERSE = prove
 (`!p s. p permutes s ==> converse(p) permutes s`,
  REL_TAC);;
```
### Informal statement
For all permutations `p` and sets `s`, if `p` permutes `s`, then `converse(p)` permutes `s`.

### Informal sketch
The proof is done automatically by `REL_TAC`, which likely relies on the definitions of `permutes` and `converse` and basic properties of relations. Essentially, If `p` is a permutation of `s` then `p` is a relation between elements of `s` such that there is a bijection. The `converse` of `p` reverses the relation such that if `(x, y)` is in `p`, then `(y, x)` is in `converse(p)`. Since `p` is a bijection it has an inverse which is a bijection from the range of `p` to its domain, so `converse(p)` is also a permutation of `s`.

### Mathematical insight
The theorem states a key property about the converse of a permutation, which is itself a permutation on the same set. This reflects the involutive nature of the converse operation when applied to permutations (i.e., taking the converse twice yields the original permutation). This also expresses the symmetry in the relationship between a set and its permutations; if a relation permutes a set, so does its inverse.

### Dependencies
- Definitions: `permutes`, `converse`

### Porting notes (optional)
This theorem should be straightforward to port, as it relies on basic definitions and properties of relations and permutations. The main challenge might be ensuring that the definitions of `permutes` and `converse` are equivalent in the target proof assistant. Also the level of automation of `REL_TAC` might not be directly available so some small unfolds and rewriting might be needed.


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
  REL_TAC);;
```

### Informal statement
For all relations `p` and `p'`, and for all `s`, `t`, and `u`, if `p` relates `(s, t)` and `p'` relates `(t, u)`, then the composition of `p` and `p'` relates `(s, u)`.

### Informal sketch
The proof proceeds by relating the composition operator to the pairsup operator.
- The theorem states that if `(s, t)` is in relation `p` and `(t, u)` is in relation `p'`, then `(s, u)` is in the relation `p % p'` (the composition of `p` and `p'`). This says that composing two relations keeps the relation between the first and last elements of the chain.
- The proof is done using `REL_TAC`, which is likely tailored for reasoning about relations in HOL Light and likely unfolds the definition of `pairsup` and relation composition and applies standard logical reasoning.

### Mathematical insight
The theorem `PAIRSUP_COMPOSE` expresses a fundamental property of relation composition: transitivity. If relation `p` connects `s` to `t` and relation `p'` connects `t` to `u`, then the composed relation `p % p'` provides a direct connection from `s` to `u`. It is important because it establishes a key behavior of composed relations.

### Dependencies
- `pairsup`
- Relation composition operator `%`.


---

## PERMUTES_COMPOSE

### Name of formal statement
PERMUTES_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_COMPOSE = prove
 (`!p p' s. p permutes s /\ p' permutes s ==> (p % p') permutes s`,
  REL_TAC);;
```
### Informal statement
For all permutations `p` and `p'` and for all sets `s`, if `p` permutes `s` and `p'` permutes `s`, then the composition `p % p'` permutes `s`.

### Informal sketch
The proof proceeds by using the `REL_TAC` tactic, which likely unfolds the definition of `permutes` and applies rewriting rules related to compositions and relations.
*   Start with the assumption that `p` permutes `s` and `p'` permutes `s`. This means that the relation corresponding to `p` is a bijection between `s` and itself, and similarly for `p'`.
*   The composition `p % p'` is proved to be a bijection since the composition of two bijections is a bijection.

### Mathematical insight
This theorem states that the composition of two permutations of a set is also a permutation of that set. It's a fundamental result in permutation theory, demonstrating closure under composition. This is crucial for showing that permutations form a group.

### Dependencies
Relevant definitions: `permutes` .

### Porting notes (optional)
The `REL_TAC` tactic in HOL Light is a high-level tactic that automates reasoning about relations. In other proof assistants, you might need to manually unfold the definition of `permutes` (likely involving a bijection) and apply theorems about the composition of bijections. You'll need to establish that the composition of bijections is a bijection in your target system. Make sure your library has a corresponding theorem on the composition of bijections.


---

## PERMUTES_SWAP

### Name of formal statement
PERMUTES_SWAP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERMUTES_SWAP = prove
 (`swap(a,b) permutes {a,b}`,
  REL_TAC);;
```
### Informal statement
The swap of `a` and `b` permutes the set `{a,b}`.

### Informal sketch
The proof uses `REL_TAC`, which likely handles the proof automatically using a pre-defined relation tactic or a set of lemmas related to permutations and sets. The formal statement states that given two elements `a` and `b`, the `swap(a, b)` function (which swaps `a` and `b` in a list) generates a permutation of the set `{a, b}`. This is because `swap(a, b)` reorders the elements within the set `{a, b}`, resulting in a permutation.

### Mathematical insight
This theorem states a basic property of the `swap` operation: that it is a permutation when applied to the set containing only the elements that are being swapped. This is a fundamental result that helps establish the relationship between transpositions (swaps) and permutations. Swaps are elementary permutations, and this theorem confirms that the `swap` function in HOL Light correctly models this behavior

### Dependencies
- Definitions: `swap`, `permutes`
- Theorems: (likely some basic lemmas about `permutes` and set operations used by `REL_TAC`)


---

## PAIRSUP_EMPTY

### Name of formal statement
PAIRSUP_EMPTY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRSUP_EMPTY = prove
 (`p pairsup ({},{}) <=> (p = {})`,
  REL_TAC);;
```

### Informal statement
For any relation `p`, `p` is the `pairsup` of the empty set `{}` and the empty set `{}` if and only if `p` is the empty set `{}`.

### Informal sketch
The theorem states that the `pairsup` of two empty sets is the empty set. The proof is done using `REL_TAC`, which likely involves reasoning directly about the relational structure defined by `pairsup`. `pairsup` presumably constructs a relation from two sets by relating each element of the first set with each element of the second set. If both sets are empty, the resulting relation is also empty since there are no pairs to be related.

### Mathematical insight
This theorem establishes a base case for reasoning about the `pairsup` relation. It demonstrates that an empty relation results when the originating sets are empty. This is a fundamental property useful in inductive proofs or when reasoning about set and relation cardinality.

### Dependencies
- Requires `REL_TAC` tactic. The content of this tactic may or may not be relevant for porting the theorem, and depends on how it is implemented in HOL Light.


---

## PAIRSUP_INSERT

### Name of formal statement
PAIRSUP_INSERT

### Type of the formal statement
theorem

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
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REL_TAC);;
```

### Informal statement
For any `x` of type `A`, sets `s` of type `A->bool`, `t` of type `B->bool`, and relation `p` of type `(A#B)->bool`, `p` holds for the pairs in the set formed by inserting `x` into `s` paired with `t` if and only if:

either `x` is in `s` and `p` holds for the pairs in the set formed by `s` paired with `t`,

or there exists a `y` of type `B` and a relation `q` of type `(A#B)->bool` such that `y` is in `t`, `p` is equal to the relation formed by inserting the pair `(x,y)` into `q`, and `q` holds for the pairs in the set formed by `s` paired with the set formed by deleting `y` from `t`.

### Informal sketch
The proof proceeds by induction on the set `s`.

- The goal is to prove the equivalence: `p pairsup (x INSERT s,t) <=> (if x IN s then p pairsup (s,t) else ?y q. y IN t /\ p = (x,y) INSERT q /\ q pairsup (s,t DELETE y))`.

- The proof uses `COND_CASES_TAC` to split the goal based on whether `x IN s`.

- If `x IN s`, then `x INSERT s = s`, so the goal simplifies to `p pairsup (s,t) <=> p pairsup (s,t)`, which is trivially true.

- If `~(x IN s)`, the goal becomes `p pairsup (x INSERT s,t) <=> ?y q. y IN t /\ p = (x,y) INSERT q /\ q pairsup (s,t DELETE y)`.

- To prove this, we first discharge the assumption to obtain `!p s t x. ~(x IN s) ==> (p pairsup (x INSERT s, t) <=> (?y q. y IN t /\ p = (x, y) INSERT q /\ q pairsup (s, t DELETE y)))`.

- Introduce an existential goal `?y. y IN t /\ p(x,y)`.  This will provide a specific `y` in `t`, allowing construction of `q`.

- Assume `y IN t /\ p(x,y)`.  By setting `q = p DELETE (x,y)` we get the result.

- Use monotonicity of `EXISTS` (`MONO_EXISTS`).

### Mathematical insight
This theorem describes how the pairs relation `pairsup` interacts with set insertion. It shows that `p pairsup (x INSERT s, t)` holds either when `x` is already in `s` and `p pairsup (s, t)` holds, or when `x` is not in `s`, in which case there must be some `y` in `t` such that the pair `(x, y)` satisfies `p` alongside a relation `q` that holds for the remaining pairs in `s` and `t \ {y}`. The `DELETE` operation in the `else` case ensures only a "minimal" relation `p` is constructed to cover `(x INSERT s, t)`.

### Dependencies
- `SET_RULE`
- `MONO_EXISTS`


---

## NUMBER_OF_PAIRINGS

### Name of formal statement
NUMBER_OF_PAIRINGS

### Type of the formal statement
theorem

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
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC]);;
```

### Informal statement
For all sets `s` of type `A` to boolean and `t` of type `B` to boolean, if `s` has size `n` and `t` has size `n`, then the set of pairings `p` such that `p` pairs up `(s, t)` has size `FACT n` (i.e., `n!`).

### Informal sketch
The proof is by induction on `n`.
- Base case (`n = 0`): If `s` and `t` are both empty, then the only pairing between them is the empty set. The size of the set containing just the empty set is 1, and `FACT 0 = 1`.
- Inductive step: Assume that for sets `s` and `t` of size `n`, the set of pairings between them has size `FACT n`.  Now consider sets `s'` and `t'` of size `n+1`. We can write `s'` as `INSERT a s` where `a` is an element not in `s`, and `s` has size `n`.  The pairings between `s'` and `t'` can be formed by taking some element `y` from `t'`, pairing `a` with `y`, and then forming a pairing between `s` and the remaining elements of `t'`. The theorem `HAS_SIZE_UNIONS` is used to show that the set of all pairings is a union of sets of pairings from an element of `t` to the remaining pairings.
The theorem `HAS_SIZE_IMAGE_INJ` is applied to show that the cardinality of `IMAGE` of the pairings after fixing initial item `a:` to item `y:` is the cardinality of the initial pairings.
The `FACT` function is rewritten to apply the factorial calculation for `n+1` and simplified using assumptions introduced in relation to sets `s` and `t`.

### Mathematical insight
This theorem establishes that if two sets, `s` and `t`, both have size `n`, then there are `n!` ways to form pairings between elements of `s` and elements of `t` such that each element in `s` is paired with exactly one element in `t`, and vice versa. This is a fundamental result in combinatorics.

### Dependencies
- `HAS_SIZE_CLAUSES`
- `PAIRSUP_EMPTY`
- `HAS_SIZE`
- `CARD_CLAUSES`
- `FINITE_RULES`
- `NOT_IN_EMPTY`
- `ARITH`
- `FACT`
- `PAIRSUP_INSERT`
- `RIGHT_EXISTS_AND_THM`
- `FACT`
- `HAS_SIZE_UNIONS`
- `HAS_SIZE_IMAGE_INJ`
- `DISJOINT`
- `EXTENSION`
- `IN_INTER`
- `IN_IMAGE`
- `NOT_IN_EMPTY`

### Porting notes (optional)
- The core logic relies on induction and set-theoretic manipulations. Encoding of sets and pairing concepts might differ in other proof assistants.
- The automatic reasoning steps (e.g. `REL_TAC`) might require manual intervention and unfolding of definitions in other systems like Coq or Lean. You would need to find an appropriate library for finite set cardinalities and factorials.


---

## NUMBER_OF_PERMUTATIONS

### Name of formal statement
NUMBER_OF_PERMUTATIONS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NUMBER_OF_PERMUTATIONS = prove
 (`!s n. s HAS_SIZE n ==> {p | p permutes s} HAS_SIZE (FACT n)`,
  SIMP_TAC[permutes; NUMBER_OF_PAIRINGS]);;
```
### Informal statement
For all sets `s` and natural numbers `n`, if the size of the set `s` is `n`, then the size of the set of permutations of `s` is `FACT n` (the factorial of `n`).

### Informal sketch
The theorem states that the number of permutations of a set of size `n` is `n!`. The proof proceeds by:
- Simplification using the definitions of `permutes` and `NUMBER_OF_PAIRINGS`.
- The definition of `permutes s` says that `p permutes s` iff the domain and range of `p` are equal to `s`, and `p` is a bijection.
- The theorem `NUMBER_OF_PAIRINGS` is used to compute the size of the set of all bijections from a set to itself.

### Mathematical insight
This theorem gives the standard result for the number of permutations of a set of finite size `n`. It connects the combinatorial notion of permutations with the factorial function.

### Dependencies
- Definitions: `permutes`
- Theorems: `NUMBER_OF_PAIRINGS`


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
The function `derangements` from natural numbers to natural numbers is defined recursively such that:
- `derangements 0` equals 1,
- `derangements 1` equals 0, and
- `derangements(n + 2)` equals `(n + 1)` multiplied by the sum of `derangements n` and `derangements(n + 1)`.

### Informal sketch
The definition of `derangements` is a primitive recursion over the natural numbers. The base cases, `derangements 0 = 1` and `derangements 1 = 0`, are defined directly. The recursive step, `derangements (n + 2) = (n + 1) * (derangements n + derangements (n + 1))`, expresses the value of `derangements` at `n + 2` in terms of its values at `n` and `n + 1`.

### Mathematical insight
The `derangements` function calculates the number of permutations of a set of *n* elements such that no element appears in its original position. The recursive definition reflects a standard combinatorial argument.

### Dependencies
None


---

## DERANGEMENT_INDUCT

### Name of formal statement
DERANGEMENT_INDUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DERANGEMENT_INDUCT = prove
 (`!P. P 0 /\ P 1 /\ (!n. P n /\ P(n + 1) ==> P(n + 2)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[ARITH]);;
```

### Informal statement
For any predicate `P` over natural numbers, if `P 0` holds, `P 1` holds, and for all `n`, if `P n` and `P (n + 1)` hold, then `P (n + 2)` holds, then `P n` holds for all natural numbers `n`.

### Informal sketch
The proof proceeds by induction.
- First, the goal is transformed into showing `!n. P n /\ P (n + 1)`. This is achieved by specializing the assumption `!P. P 0 /\ P 1 /\ (!n. P n /\ P(n + 1) ==> P(n + 2)) ==> !n. P n` (using `GEN_TAC` & `STRIP_TAC`) and then using `MESON_TAC` to derive it.
- Then, induction is applied on `n`.
    - The base case involves demonstrating that `P 0` and `P 1` hold, which is immediate from the assumptions that `P 0` and `P 1` hold.
    - The inductive step assumes `P n` and `P (n + 1)` hold, and aims to prove `P (n + 1)` and `P (n + 2)`. The assumption `!n. P n /\ P(n + 1) ==> P(n + 2)` can be applied to obtain `P(n + 2)` given `P n` and `P (n + 1)`. The simplification steps using `ADD1` and `GSYM ADD_ASSOC` together with `ARITH` is used to resolve the arithmetic reasoning implicitly.

### Mathematical insight
This theorem establishes the principle of strong induction for natural numbers, where instead of just needing to prove `P(n+1)` from `P(n)`, we prove `P(n+2)` from `P(n)` and `P(n+1)`. This is useful when you have a recursive definition or property that depends on the two previous values, similar to Fibonacci numbers.

### Dependencies
- `ADD1`
- `ADD_ASSOC`
- `ARITH`


---

## DERANGEMENT_ADD2

### Name of formal statement
DERANGEMENT_ADD2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DERANGEMENT_ADD2 = prove
 (`!p s x y.
        p deranges s /\ ~(x IN s) /\ ~(y IN s) /\ ~(x = y)
        ==> ((x,y) INSERT (y,x) INSERT p) deranges (x INSERT y INSERT s)`,
  REL_TAC);;
```
### Informal statement
For all permutations `p`, sets `s`, and elements `x` and `y`, if `p` is a derangement of `s`, `x` is not in `s`, `y` is not in `s`, and `x` is not equal to `y`, then the permutation formed by inserting the pairs `(x, y)` and `(y, x)` into `p` is a derangement of the set formed by inserting `x` and `y` into `s`.

### Informal sketch
The proof proceeds by showing that adding the pairs `(x, y)` and `(y, x)` to the derangement `p` and adding `x` and `y` to the set `s` preserves the derangement property.
- The assumption `p deranges s` means that for every `z` in `s`, `p z` is not `z`.
- We need to show that `((x,y) INSERT (y,x) INSERT p) deranges (x INSERT y INSERT s)`.
- This requires showing that for every `z` in `x INSERT y INSERT s`, `((x,y) INSERT (y,x) INSERT p) z` is not `z`.
- There are three cases to consider: `z = x`, `z = y`, and `z` is in `s`.
  - If `z = x`, then `((x,y) INSERT (y,x) INSERT p) x = y`, and since `x` is not `y`, the property holds.
  - If `z = y`, then `((x,y) INSERT (y,x) INSERT p) y = x`, and since `y` is not `x`, the property holds.
  - If `z` is in `s`, then `((x,y) INSERT (y,x) INSERT p) z = p z`. Since `p` deranges `s`, `p z` is not `z`.  Also, since `x` and `y` are not in `s`, `p z` cannot be `x` or `y`. Thus, adding the pairs `(x, y)` and `(y, x)` does not affect the derangement property for elements in `s`.
- REL_TAC is used to resolve equality assumptions

### Mathematical insight
This theorem demonstrates how to extend a derangement by adding two new elements to the set and updating the permutation accordingly. The key idea is to ensure that the new permutation maps each new element to the other and that the original elements in the set still satisfy the derangement property under the extended permutation.

### Dependencies
- `deranges`
- `IN`
- `INSERT`


---

## DERANGEMENT_ADD1

### Name of formal statement
DERANGEMENT_ADD1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DERANGEMENT_ADD1 = prove
 (`!p s y x. p deranges s /\ ~(y IN s) /\ p(x,z)
             ==> ((x,y) INSERT (y,z) INSERT (p DELETE (x,z)))
                 deranges (y INSERT s)`,
  REL_TAC);;
```
### Informal statement
For all permutations `p`, sets `s`, and elements `y` and `x`, if `p` deranges `s`, `y` is not in `s`, and `p(x) = z`, then the permutation obtained by inserting the pair `(x, y)` and the pair `(y, z)` into `p` and deleting the pair `(x, z)` from `p` deranges the set `y INSERT s`.

### Informal sketch
- The theorem states that we can construct a new derangement from an existing one by "inserting" an element `y` not already in the set being deranged.
- Suppose `p` is a derangement of `s` and `y` is not in `s`.
- We pick an arbitrary `x` in `s` and suppose `p(x) = z`.
- We construct `p'` by removing `(x,z)` from `p` and inserting `(x,y)` and `(y,z)`. In HOL Light, `p DELETE (x,z)` computes the result of removing the pair `(x,z)` from the graph of `p`, while `(x,y) INSERT (y,z) INSERT (p DELETE (x,z))` represents adding the relation `x -> y` and `y -> z` to the relation `p` with the aforementioned pair deleted.
- We need to show that `p'` deranges `y INSERT s`.
- This means showing that for all `a` in `y INSERT s`, we have `p'(a) != a`.
  - If `a = y`, then `p'(y) = z`. Since `p` deranges `s`, `z` is not `x` (since `x` is in `s`). Because `y` is not in `s`, `y` and `z` are distinct.
  - If `a` is in `s` and `a != x`, then `p'(a) = p(a)`. Since `p` deranges `s`, `p(a) != a`.
  - If `a = x`, then `p'(x) = y`. But since `x` is in `s` and `y` is not, `x != y`.

### Mathematical insight
The theorem shows how to extend a derangement by adding a new element. The core idea is to "redirect" the mapping of an existing element in the set to the new element and then map the new element to where the original mapping pointed. This effectively inserts the new element into the derangement while preserving the derangement property. This is useful for inductively constructing derangements of larger sets.

### Dependencies
None

### Porting notes (optional)
This theorem involves reasoning about permutations represented as sets of pairs. In translating this theorem, one may need to consider how permutations and set operations are represented in the target proof assistant. The `INSERT` and `DELETE` operations on relations will need to be defined appropriately to maintain the intended meaning. Tactics that support reasoning about relations and set membership would be useful for porting the proof.


---

## DERANGEMENT_EMPTY

### Name of formal statement
DERANGEMENT_EMPTY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DERANGEMENT_EMPTY = prove
 (`!p. p deranges {} <=> p = {}`,
  REL_TAC);;
```

### Informal statement
For all predicates `p` on sets, `p` deranges the empty set if and only if `p` is equal to the empty set.

### Informal sketch
The proof uses `REL_TAC`, which likely means it relies on the extensionality rule for relations (or, in this case, predicates on sets, viewed as relations to the boolean values), and basic properties of the `deranges` predicate. The theorem essentially states that the only predicate which is true for a derangement of the empty set is the predicate that is only true for the empty set itself.

*   The definition of `deranges` likely involves a quantification over elements of the set such that no element maps to itself under a given permutation. Since the empty set has no elements, the quantification is trivially true for the empty function (which is also usually the empty set in HOL Light).
*   The right-to-left implication is trivial; if `p` is the empty set, then `p` deranges the empty set.
*   The left-to-right implication requires us to show that if `p` deranges the empty set, then `p` *is* the empty set. This hinges on the fact that, for the empty set, vacuous quantification makes every predicate true.

### Mathematical insight
This theorem establishes a fundamental property of derangements acting on the empty set. It highlights the "vacuously true" nature of statements quantifying over the empty set. Since a derangement requires that no element maps to itself, and the empty set has no elements, any candidate permutation is vacuously a derangement. The theorem formalizes this intuition by linking predicates that characterize derangements to the identity predicate on the empty set.

### Dependencies
*   Definition of `deranges` probably relies on set theory and predicate logic.

### Porting notes (optional)
In other proof assistants (e.g., Coq, Lean), the key is to ensure the correct handling of quantification over empty sets and the extensionality of relations (or sets). The `REL_TAC` tactic suggests a reliance on extensionality.


---

## DERANGEMENT_SING

### Name of formal statement
DERANGEMENT_SING

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DERANGEMENT_SING = prove
 (`!x p. ~(p deranges {x})`,
  REL_TAC);;
```

### Informal statement
For all `x` and `p`, it is not the case that `p` deranges the singleton set containing `x`.

### Informal sketch
The theorem states that no permutation `p` can derange a singleton set. This is shown using `REL_TAC`, which likely unfolds definitions related to `deranges`. The core idea is that for a permutation to derange a set `s`, it must map every element of `s` to an element that is not itself. A singleton set `{x}` contains only one element `x`.  Any permutation applied to `x` *must* map it to *some* element. Therefore, it can not map `x` to a value that is not `x` while also satisfying the requirement of applying to all elements of the set.

### Mathematical insight
The theorem expresses a basic property of derangements: a single element cannot be deranged. This is important because it highlights a corner case of the `deranges` predicate, which is crucial when reasoning about permutations and their actions on sets.

### Dependencies
- Definitions: `deranges`

### Porting notes (optional)
- Ensure the definition of `deranges` is available in the target proof assistant.
- Depending on the automation available, the proof might require unfolding the definition of `deranges` and applying basic logical reasoning.


---

## NUMBER_OF_DERANGEMENTS

### Name of formal statement
NUMBER_OF_DERANGEMENTS

### Type of the formal statement
theorem

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
    REPEAT(POP_ASSUM MP_TAC) THEN REL_TAC]);;
```
### Informal statement
For any `n` of type `num` and any set `s` of type `A->bool`, if `s` has size `n`, then the set of permutations `p` that derange `s` has size `derangements n`.

### Informal sketch
The proof proceeds by induction on the size of set `s`, i.e., on `n`. The base cases are for `n = 0` and `n = 1`. The inductive step requires showing that if a set `s` of size `n+2` exists, then the number of derangements of `s` is equal to `derangements (n+2)`. This is done by relating the derangements of `s` to derangements of its subsets.

- Base Case (n=0): The empty set has size 0, and the set of derangements of the empty set has size `derangements 0`, i.e., 1.
- Base Case (n=1): A singleton set has size 1, and the set of derangements of such a set is empty and has size `derangements 1`, i.e., 0.
- Inductive Step: Assume the theorem holds for `n` and `n+1`. We want to show it holds for `n+2`. Given a set `s` of size `n+2`, we express derangements of `s` through elements `x, y` in `s`, and permutations `p` which derange the set by swapping `x` and `y` i.e `(x,y)(y,x)`. The expression `{p | p deranges (x:A INSERT s)}` is split into two cases
    - Case 1: considers swapping `x` with another element `y` along with permutations `p` of `s DELETE y`. This is formalized using `IMAGE (\(y,p). (x,y) INSERT (y,x) INSERT p) {(y,p) | y IN s /\ p IN {p | p deranges (s DELETE y)}}`
    - Case 2: consider any pair `x,y` and a z which is the element where `p(x,z)` after the swap. This is formalized using  `IMAGE (\(y,p). let z = @z. p(x,z) in (x,y) INSERT (y,z) INSERT (p DELETE (x,z))) {(y,p) | y IN s /\ p IN {p | p deranges (x INSERT (s DELETE y))}}`
- After rewriting and simplification steps, the proof uses facts about `HAS_SIZE_UNION`, `HAS_SIZE_IMAGE_INJ`, `HAS_SIZE_PRODUCT_DEPENDENT`, and disjointness to complete the inductive step, and then finishes automatically.

### Mathematical insight
The theorem gives the number of derangements of a set of size `n`, where a derangement is a permutation that leaves no element in its original position. This quantity appears in various combinatorial problems. The proof is a fairly standard inductive argument, which uses the identity `derangements (n+2) = (n+1) * (derangements n + derangements (n+1))`.

### Dependencies
- Definitions: `derangements`
- Theorems: `DERANGEMENT_INDUCT`, `DERANGEMENT_EMPTY`, `EXTENSION`, `IN_ELIM_THM`, `NOT_IN_EMPTY`, `IN_SING`, `MEMBER_NOT_EMPTY`, `DERANGEMENT_SING`, `DERANGEMENT_ADD2`, `DERANGEMENT_ADD1`, `HAS_SIZE_CLAUSES`, `LEFT_IMP_EXISTS_THM`, `HAS_SIZE_UNION`, `HAS_SIZE_IMAGE_INJ`, `HAS_SIZE_PRODUCT_DEPENDENT`, `HAS_SIZE_CONV`, `ARITH_RULE`, `LEFT_ADD_DISTRIB`,`SELECT_UNIQUE`
- Other Rules: `SET_RULE`

### Porting notes (optional)
- The `derangements` function might need explicit definition based on the target proof assistant.
- The use of choice operator `@` in HOL Light to select an element `z` such that `p(x, z)` might require special handling in other systems. Lean's `epsilon` or Coq's `HilbertChoice` might be relevant.
- Consider the automation level provided by the target prover for set theory reasoning.


---

## SUM_1

### Name of formal statement
SUM_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_1 = prove
 (`sum(0..1) f = f 0 + f 1`,
  REWRITE_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0]);;
```

### Informal statement
For any function `f`, the sum of `f i` where `i` ranges from 0 to 1 inclusive, equals `f 0 + f 1`.

### Informal sketch
The theorem states an expansion of the sum over a numeric segment from 0 to 1. The proof proceeds by:
- Evaluating the numeric expression `1` using `num_CONV \`1\`` which probably fully normalizes it, but in this simple case does not do much.
- Applying the theorem `SUM_CLAUSES_NUMSEG`. This likely expands the sum over the segment `0..1`, which should be a standard theorem about sums over numeric segments in library `SUM`.
- Applying the lemma `LE_0` or rewriting using judgement `LE_0`. This likely involves handling the less-than-or-equal-to comparison that may arise inside the definition of `sum` over a numeric segment.

### Mathematical insight
The theorem expresses a basic but important property of sums over numeric ranges: when the range consists of just two numbers, the sum is simply the sum of the function applied to each of the numbers. This is a fundamental property used in manipulating sums in various contexts.

### Dependencies
- Theorems: `SUM_CLAUSES_NUMSEG`, `LE_0`
- Conversion: `num_CONV \`1\``


---

## SUM_2

### Name of formal statement
SUM_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_2 = prove
 (`sum(0..2) f = f 0 + f 1 + f 2`,
  SIMP_TAC[num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0;
           REAL_ADD_AC]);;
```
### Informal statement
The sum of `f i` where `i` ranges from 0 to 2 is equal to `f 0 + f 1 + f 2`.

### Informal sketch
The proof uses the following steps:
- Expand sum using `SUM_CLAUSES_NUMSEG` to recursively break down the sum over the number segment `0..2`. This clause likely recursively reduces `sum(m..n) f` to `f m + sum(m+1..n) f`.
- Evaluate the resulting arithmetic using `num_CONV` to reduce the numeral terms `2` and `1`.
- Apply `LE_0` to discharge the condition `0 <= 0`.
- Use `REAL_ADD_AC` to reassociate the real addition.

### Mathematical insight
This theorem provides a basic expansion of a summation over a concrete range of natural numbers. It concretely expands what `sum(0..2) f` means.

### Dependencies
- Theorems: `SUM_CLAUSES_NUMSEG`, `LE_0`
- Conversions: `num_CONV`, `REAL_ADD_AC`


---

## DERANGEMENTS

### Name of formal statement
DERANGEMENTS

### Type of the formal statement
theorem

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
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For all natural numbers `n`, if `n` is not equal to 0, then the real number representation of `derangements n` is equal to the real number representation of `FACT n` multiplied by the sum from 0 to `n` of the expression `(-1)^k / FACT k`, where `k` is the index of summation.

### Informal sketch
The proof proceeds by induction on the number of elements `n`.

- Base case: `n = 1`. The theorem is proved using simplification rules for arithmetic, `derangements`, and sums (`SUM_1`). Real number conversions and rational number reductions are also applied.
- Inductive step: Assume the theorem holds for some `n`. We want to show it holds for `n + 2`.
  - Split into two subgoals based on whether `n = 0`.

     - Subgoal 1 (`n = 0`): Rewrite using `derangements`, arithmetic rules, and summation rules (`SUM_2; SUM_1`). Simplify using number and rational conversions. Conclude with `ALL_TAC`.

     - Subgoal 2 (`~(n = 0)`): Use the inductive hypothesis, rewrite arithmetic facts (e.g., `n + 2 = (n + 1) + 1`), split the summation (`SUM_ADD_SPLIT`), and simplify. Employ previously established facts about factorials (`FACT_LT`), real powers (`REAL_POW_NEG`), conversions between naturals and reals, and field arithmetic (`REAL_FIELD`).

### Mathematical insight
The theorem gives a closed-form expression for the number of derangements of `n` elements. A derangement is a permutation of a set such that no element appears in its original position. The number of derangements can be expressed as `n!` multiplied by a truncated series expansion of `e^{-1}`.

### Dependencies
- Definitions: `derangements`, `FACT`
- Theorems/Lemmas: `ADD_EQ_0`, `ARITH_EQ`, `SUM_1`, `SUM_2`, `GSYM REAL_OF_NUM_MUL`, `GSYM REAL_OF_NUM_ADD`, `ARITH_RULE n + 2 = (n + 1) + 1`, `SUM_ADD_SPLIT`, `LE_0`, `SUM_SING_NUMSEG`, `GSYM ADD1`, `real_pow`, `SUC(SUC n) = n + 2`, `GSYM REAL_OF_NUM_SUC`, `FACT_LT`, `GSYM LT_NZ`, `REAL_POW_NEG`, `REAL_POW_ONE`

### Porting notes (optional)
- The proof relies heavily on rewriting and simplification with various arithmetic and real number rules. Other proof assistants might require more explicit manipulation of these rules.
- The conversion tactics (`NUM_REDUCE_CONV`, `REAL_RAT_REDUCE_CONV`, `REAL_FIELD`) might have direct equivalents in other systems, or custom tactics may need to be developed.
- Special attention should be given to the real number conversions from natural numbers. Different proof assistants may handle them differently.


---

## DERANGEMENTS_EXP

### Name of formal statement
DERANGEMENTS_EXP

### Type of the formal statement
theorem

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
  REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, if `n` is not equal to 0, then, letting `e` be the exponential of 1, the absolute value of the difference between the number of derangements of `n` and `FACT n` divided by `e` is less than 1/2.

### Informal sketch
The proof proceeds by induction-like reasoning, splitting into two cases:

- Case 1: `n < 5`. This is handled by explicit computation for `n = 1, 2, 3, 4`. The values of `derangements n` and `FACT n` are computed, and the inequality is verified directly.
- Case 2: `~(n < 5)`.
  - McLaurin's expansion is used on `exp(-1)`
  - Bound the error using `u:real` and the inequality `abs(u) <= abs(-- &1)` showing the existence of a real number to make the error bound valid.
  - Show that the upper bound is less than or equal to 3, thefore the error is less than 1/2 using `REAL_LTE_TRANS` and a real calculation step, using the assertion `~(n < 5)`.

### Mathematical insight
The theorem provides an approximation to the number of derangements of a set of size `n`. It states that the number of derangements is approximately `FACT n / e`, where `e` is the base of the natural logarithm. The error in this approximation is less than 1/2. This is a useful result in combinatorics and probability theory, as it allows one to estimate the number of derangements without having to compute it exactly.

### Dependencies
- Definitions: `DERANGEMENTS`, `LET_DEF`, `LET_END_DEF`
- Theorems: `real_div`, `GSYM REAL_EXP_NEG`, `MCLAURIN_EXP_LE`, `PSUM_SUM_NUMSEG`, `ADD_EQ_0`, `ARITH_EQ`, `REAL_EXP_POS_LE`, `REAL_LET_TRANS`, `REAL_EXP_MONO_LE`, `REAL_LTE_TRANS`, `NOT_LT`, `GSYM REAL_OF_NUM_LE`


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
The function `round` is defined such that, for any real number `x`, `round x` is equal to some integer `n` such that `n - 1/2 <= x` and `x < n + 1/2`. In other words, `round x` returns an integer `n` that is within one-half of `x`.

### Informal sketch
- The definition introduces a function called `round`, which maps a real number to an integer.
- The definition uses Hilbert choice operator `@` to pick an integer `n` satisfying the condition `integer(n) /\ n - &1 / &2 <= x /\ x < n + &1 / &2`. This condition states that `n` is an integer and that `x` lies in the interval `[n - 1/2, n + 1/2)`.  In other words the real number `x` is rounded to the nearest integer `n`.

### Mathematical insight
The `round` function maps a real number to the nearest integer. While multiple such integers might exist if x is exactly of the form `n + 1/2`, the Hilbert choice operator ensures that the function returns one such integer consistently. Specifically, if `x = n + 1/2` for some integer `n`, and both `n` and `n+1` would satisfy the condition, the choice operator will pick one. Note that, the rounding is half-up, as `round (n + 1/2) = n + 1` but `round (n - 1/2) = n`.

### Dependencies
- `integer` : predicate that returns true if the input is an integer.


---

## ROUND_WORKS

### Name of formal statement
ROUND_WORKS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ROUND_WORKS = prove
 (`!x. integer(round x) /\ round x - &1 / &2 <= x /\ x < round x + &1 / &2`,
  GEN_TAC THEN REWRITE_TAC[round] THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `floor(x + &1 / &2)` THEN MP_TAC(SPEC `x + &1 / &2` FLOOR) THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers `x`, `round x` is an integer, and `round x - 1/2 <= x` and `x < round x + 1/2`.

### Informal sketch
The proof proceeds as follows:
- It starts by rewriting `round x` to `floor(x + &1 / &2)`.
- Then an existential instantiation is performed using `floor(x + &1 / &2)`
- Then, using the theorem `FLOOR`, namely `!x. x <= floor x + &1 /\ floor x <= x`, we prove `floor x <= x /\ x <= floor x + &1` which will reduce to the desired inequalities.
- Then `INTEGER_CLOSED` asserts that `floor n` is an integer if `n` is a real.
- Finally, `REAL_ARITH_TAC` completes the proof via real number arithmetic.

### Mathematical insight
This theorem establishes the fundamental property of the `round` function, namely that it returns an integer, it is within 1/2 of the original number, and that `round x` is defined as `floor(x + 1/2)`.

### Dependencies
- Definitions: `round`
- Theorems: `FLOOR`, `INTEGER_CLOSED`


---

## DERANGEMENTS_EXP

### Name of formal statement
DERANGEMENTS_EXP

### Type of the formal statement
theorem

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
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REAL_ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, if `n` is not equal to 0, then if `e` is equal to `exp(&1)` (where `exp` is the exponential function and `&1` is the real representation of the natural number 1), then the real representation of `derangements n` is equal to the rounding of the real representation of `FACT n` divided by `e` (where `FACT n` is the factorial of `n`).

### Informal sketch
The proof proceeds by induction on `n`.

- The base case where `n = 0` is excluded by the initial condition `~(n = 0)`.
- Then, the goal is rewritten using several theorems and definitions, including `INTEGER_CLOSED`, `ROUND_WORKS`, `LET_DEF`, and `LET_END_DEF`.
- The definition of `derangements n` and its relation to the exponential function `e` is exploited.
- Finally, the proof concludes using real arithmetic.

### Mathematical insight
This theorem provides a useful approximation for the number of derangements of a set of size `n`. It states that the number of derangements is approximately equal to `n! / e`, where `e` is Euler's number. This approximation becomes more accurate as `n` increases. The theorem shows that the real representation of the number of derangements is the nearest integer to `n! / e`.

### Dependencies
- Theorems: `REAL_EQ_INTEGERS_IMP`, `INTEGER_CLOSED`, `ROUND_WORKS`
- Definitions: `LET_DEF`, `LET_END_DEF`


---

## THE_DERANGEMENTS_FORMULA

### Name of formal statement
THE_DERANGEMENTS_FORMULA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let THE_DERANGEMENTS_FORMULA = prove
 (`!n s. s HAS_SIZE n /\ ~(n = 0)
         ==> FINITE {p | p deranges s} /\
             let e = exp(&1) in
             &(CARD {p | p deranges s}) = round(&(FACT n) / e)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP NUMBER_OF_DERANGEMENTS) THEN
  ASM_SIMP_TAC[HAS_SIZE; DERANGEMENTS_EXP]);;
```
### Informal statement
For all `n` and `s`, if `s` has size `n` and `n` is not equal to 0, then the set of permutations of `s` that are derangements is finite, and the cardinality of the set of permutations of `s` that are derangements is equal to the nearest integer to `n!` divided by `e`, where `e` is the exponential of 1.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifiers and implications using `REPEAT STRIP_TAC`.
- Apply `NUMBER_OF_DERANGEMENTS` to the assumption using `FIRST_X_ASSUM(MP_TAC o MATCH_MP NUMBER_OF_DERANGEMENTS)`. `NUMBER_OF_DERANGEMENTS` is a theorem quantifying the number of derangements. This step essentially uses the theorem of the number of derangements to rewrite a statement concerning `{p | p deranges s}`.
- Simplify using assumptions and the theorems `HAS_SIZE` and `DERANGEMENTS_EXP` via `ASM_SIMP_TAC[HAS_SIZE; DERANGEMENTS_EXP]`. The `DERANGEMENTS_EXP` probably states that the number of derangements approaches `n!/e`, where `e` is the exponential constant.

### Mathematical insight
The theorem gives a formula for the number of derangements of a set of size `n`. A derangement is a permutation in which no element remains in its original position. This formula approximates the number of derangements as `n!/e`, where `e` is Euler's number, and then rounds to the nearest integer. This result is important in combinatorics and has applications in various fields.

### Dependencies
- `HAS_SIZE`
- `NUMBER_OF_DERANGEMENTS`
- `DERANGEMENTS_EXP`


---

